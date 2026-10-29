-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1726_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:01:24.66866+00:00
-- url     : https://prove2.me/submissions/c62e71c4-9e6a-49c5-a54e-56b466bf63dd

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
theorem support_rectangle_w1726_s0_0 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-645392967/5000000000 : ℝ)*x 0 + (5666974523/10000000000 : ℝ)*x 1 + (995279143/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (645392967/5000000000 : ℝ)^5431 ≤ (250671209107/3125000000000 : ℝ)^4407 := by
    have hnat : (645392967 : ℕ)^5431*3125000000000^4407 ≤ 250671209107^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645392967 5000000000 250671209107 3125000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5666974523/10000000000 : ℝ)^5431 ≤ (49663868782067/100000000000000 : ℝ)^4407 := by
    have hnat : (5666974523 : ℕ)^5431*100000000000000^4407 ≤ 49663868782067^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5666974523 10000000000 49663868782067 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995279143/2000000000 : ℝ)^5431 ≤ (10578663129261/25000000000000 : ℝ)^4407 := by
    have hnat : (995279143 : ℕ)^5431*25000000000000^4407 ≤ 10578663129261^4407*2000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995279143 2000000000 10578663129261 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-645392967/5000000000 : ℝ), (5666974523/10000000000 : ℝ), (995279143/2000000000 : ℝ)] ![(250671209107/3125000000000 : ℝ), (49663868782067/100000000000000 : ℝ), (10578663129261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-645392967/5000000000 : ℝ)|^5431 ≤ (250671209107/3125000000000 : ℝ)^4407
        have hw : |(-645392967/5000000000 : ℝ)|=(645392967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5666974523/10000000000 : ℝ)|^5431 ≤ (49663868782067/100000000000000 : ℝ)^4407
        have hw : |(5666974523/10000000000 : ℝ)|=(5666974523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(995279143/2000000000 : ℝ)|^5431 ≤ (10578663129261/25000000000000 : ℝ)^4407
        have hw : |(995279143/2000000000 : ℝ)|=(995279143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s0_1 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348331077/2500000000 : ℝ)*x 0 + (-831430419/5000000000 : ℝ)*x 1 + (4976395083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348331077/2500000000 : ℝ)^5431 ≤ (46725220609497/100000000000000 : ℝ)^4407 := by
    have hnat : (1348331077 : ℕ)^5431*100000000000000^4407 ≤ 46725220609497^4407*2500000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348331077 2500000000 46725220609497 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (831430419/5000000000 : ℝ)^5431 ≤ (2192026696671/20000000000000 : ℝ)^4407 := by
    have hnat : (831430419 : ℕ)^5431*20000000000000^4407 ≤ 2192026696671^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831430419 5000000000 2192026696671 20000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4976395083/10000000000 : ℝ)^5431 ≤ (21157322947213/50000000000000 : ℝ)^4407 := by
    have hnat : (4976395083 : ℕ)^5431*50000000000000^4407 ≤ 21157322947213^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4976395083 10000000000 21157322947213 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348331077/2500000000 : ℝ), (-831430419/5000000000 : ℝ), (4976395083/10000000000 : ℝ)] ![(46725220609497/100000000000000 : ℝ), (2192026696671/20000000000000 : ℝ), (21157322947213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348331077/2500000000 : ℝ)|^5431 ≤ (46725220609497/100000000000000 : ℝ)^4407
        have hw : |(1348331077/2500000000 : ℝ)|=(1348331077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-831430419/5000000000 : ℝ)|^5431 ≤ (2192026696671/20000000000000 : ℝ)^4407
        have hw : |(-831430419/5000000000 : ℝ)|=(831430419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4976395083/10000000000 : ℝ)|^5431 ≤ (21157322947213/50000000000000 : ℝ)^4407
        have hw : |(4976395083/10000000000 : ℝ)|=(4976395083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s0_2 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393323027/10000000000 : ℝ)*x 0 + (2488197937/5000000000 : ℝ)*x 1 + (-1662861501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393323027/10000000000 : ℝ)^5431 ≤ (2920325433301/6250000000000 : ℝ)^4407 := by
    have hnat : (5393323027 : ℕ)^5431*6250000000000^4407 ≤ 2920325433301^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393323027 10000000000 2920325433301 6250000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2488197937/5000000000 : ℝ)^5431 ≤ (42314654183177/100000000000000 : ℝ)^4407 := by
    have hnat : (2488197937 : ℕ)^5431*100000000000000^4407 ≤ 42314654183177^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2488197937 5000000000 42314654183177 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1662861501/10000000000 : ℝ)^5431 ≤ (10960138868659/100000000000000 : ℝ)^4407 := by
    have hnat : (1662861501 : ℕ)^5431*100000000000000^4407 ≤ 10960138868659^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1662861501 10000000000 10960138868659 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393323027/10000000000 : ℝ), (2488197937/5000000000 : ℝ), (-1662861501/10000000000 : ℝ)] ![(2920325433301/6250000000000 : ℝ), (42314654183177/100000000000000 : ℝ), (10960138868659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393323027/10000000000 : ℝ)|^5431 ≤ (2920325433301/6250000000000 : ℝ)^4407
        have hw : |(5393323027/10000000000 : ℝ)|=(5393323027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2488197937/5000000000 : ℝ)|^5431 ≤ (42314654183177/100000000000000 : ℝ)^4407
        have hw : |(2488197937/5000000000 : ℝ)|=(2488197937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1662861501/10000000000 : ℝ)|^5431 ≤ (10960138868659/100000000000000 : ℝ)^4407
        have hw : |(-1662861501/10000000000 : ℝ)|=(1662861501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s0_3 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (31455743/78125000 : ℝ)*x 0 + (122765701/400000000 : ℝ)*x 1 + (5144519757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31455743/78125000 : ℝ)^5431 ≤ (8147938414691/25000000000000 : ℝ)^4407 := by
    have hnat : (31455743 : ℕ)^5431*25000000000000^4407 ≤ 8147938414691^4407*78125000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31455743 78125000 8147938414691 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122765701/400000000 : ℝ)^5431 ≤ (11662497639843/50000000000000 : ℝ)^4407 := by
    have hnat : (122765701 : ℕ)^5431*50000000000000^4407 ≤ 11662497639843^4407*400000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122765701 400000000 11662497639843 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5144519757/10000000000 : ℝ)^5431 ≤ (22041625525377/50000000000000 : ℝ)^4407 := by
    have hnat : (5144519757 : ℕ)^5431*50000000000000^4407 ≤ 22041625525377^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144519757 10000000000 22041625525377 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(31455743/78125000 : ℝ), (122765701/400000000 : ℝ), (5144519757/10000000000 : ℝ)] ![(8147938414691/25000000000000 : ℝ), (11662497639843/50000000000000 : ℝ), (22041625525377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(31455743/78125000 : ℝ)|^5431 ≤ (8147938414691/25000000000000 : ℝ)^4407
        have hw : |(31455743/78125000 : ℝ)|=(31455743/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(122765701/400000000 : ℝ)|^5431 ≤ (11662497639843/50000000000000 : ℝ)^4407
        have hw : |(122765701/400000000 : ℝ)|=(122765701/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5144519757/10000000000 : ℝ)|^5431 ≤ (22041625525377/50000000000000 : ℝ)^4407
        have hw : |(5144519757/10000000000 : ℝ)|=(5144519757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s0_4 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-646112947/5000000000 : ℝ)*x 0 + (4993066799/10000000000 : ℝ)*x 1 + (353110357/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646112947/5000000000 : ℝ)^5431 ≤ (4016253941211/50000000000000 : ℝ)^4407 := by
    have hnat : (646112947 : ℕ)^5431*50000000000000^4407 ≤ 4016253941211^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646112947 5000000000 4016253941211 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4993066799/10000000000 : ℝ)^5431 ≤ (42489413836313/100000000000000 : ℝ)^4407 := by
    have hnat : (4993066799 : ℕ)^5431*100000000000000^4407 ≤ 42489413836313^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4993066799 10000000000 42489413836313 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (353110357/625000000 : ℝ)^5431 ≤ (49478078266417/100000000000000 : ℝ)^4407 := by
    have hnat : (353110357 : ℕ)^5431*100000000000000^4407 ≤ 49478078266417^4407*625000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353110357 625000000 49478078266417 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-646112947/5000000000 : ℝ), (4993066799/10000000000 : ℝ), (353110357/625000000 : ℝ)] ![(4016253941211/50000000000000 : ℝ), (42489413836313/100000000000000 : ℝ), (49478078266417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-646112947/5000000000 : ℝ)|^5431 ≤ (4016253941211/50000000000000 : ℝ)^4407
        have hw : |(-646112947/5000000000 : ℝ)|=(646112947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4993066799/10000000000 : ℝ)|^5431 ≤ (42489413836313/100000000000000 : ℝ)^4407
        have hw : |(4993066799/10000000000 : ℝ)|=(4993066799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(353110357/625000000 : ℝ)|^5431 ≤ (49478078266417/100000000000000 : ℝ)^4407
        have hw : |(353110357/625000000 : ℝ)|=(353110357/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s0_5 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5206730681/10000000000 : ℝ)*x 0 + (-989490549/10000000000 : ℝ)*x 1 + (2824882919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5206730681/10000000000 : ℝ)^5431 ≤ (11185280239681/25000000000000 : ℝ)^4407 := by
    have hnat : (5206730681 : ℕ)^5431*25000000000000^4407 ≤ 11185280239681^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206730681 10000000000 11185280239681 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (989490549/10000000000 : ℝ)^5431 ≤ (1445199851551/25000000000000 : ℝ)^4407 := by
    have hnat : (989490549 : ℕ)^5431*25000000000000^4407 ≤ 1445199851551^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989490549 10000000000 1445199851551 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2824882919/5000000000 : ℝ)^5431 ≤ (49478079626263/100000000000000 : ℝ)^4407 := by
    have hnat : (2824882919 : ℕ)^5431*100000000000000^4407 ≤ 49478079626263^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2824882919 5000000000 49478079626263 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5206730681/10000000000 : ℝ), (-989490549/10000000000 : ℝ), (2824882919/5000000000 : ℝ)] ![(11185280239681/25000000000000 : ℝ), (1445199851551/25000000000000 : ℝ), (49478079626263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5206730681/10000000000 : ℝ)|^5431 ≤ (11185280239681/25000000000000 : ℝ)^4407
        have hw : |(5206730681/10000000000 : ℝ)|=(5206730681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-989490549/10000000000 : ℝ)|^5431 ≤ (1445199851551/25000000000000 : ℝ)^4407
        have hw : |(-989490549/10000000000 : ℝ)|=(989490549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2824882919/5000000000 : ℝ)|^5431 ≤ (49478079626263/100000000000000 : ℝ)^4407
        have hw : |(2824882919/5000000000 : ℝ)|=(2824882919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s0_6 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2603365157/5000000000 : ℝ)*x 0 + (2824882887/5000000000 : ℝ)*x 1 + (-61843199/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2603365157/5000000000 : ℝ)^5431 ≤ (894822341447/2000000000000 : ℝ)^4407 := by
    have hnat : (2603365157 : ℕ)^5431*2000000000000^4407 ≤ 894822341447^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603365157 5000000000 894822341447 2000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2824882887/5000000000 : ℝ)^5431 ≤ (12369519733887/25000000000000 : ℝ)^4407 := by
    have hnat : (2824882887 : ℕ)^5431*25000000000000^4407 ≤ 12369519733887^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2824882887 5000000000 12369519733887 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (61843199/625000000 : ℝ)^5431 ≤ (5780803977999/100000000000000 : ℝ)^4407 := by
    have hnat : (61843199 : ℕ)^5431*100000000000000^4407 ≤ 5780803977999^4407*625000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61843199 625000000 5780803977999 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2603365157/5000000000 : ℝ), (2824882887/5000000000 : ℝ), (-61843199/625000000 : ℝ)] ![(894822341447/2000000000000 : ℝ), (12369519733887/25000000000000 : ℝ), (5780803977999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2603365157/5000000000 : ℝ)|^5431 ≤ (894822341447/2000000000000 : ℝ)^4407
        have hw : |(2603365157/5000000000 : ℝ)|=(2603365157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2824882887/5000000000 : ℝ)|^5431 ≤ (12369519733887/25000000000000 : ℝ)^4407
        have hw : |(2824882887/5000000000 : ℝ)|=(2824882887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-61843199/625000000 : ℝ)|^5431 ≤ (5780803977999/100000000000000 : ℝ)^4407
        have hw : |(-61843199/625000000 : ℝ)|=(61843199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s0_7 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4030660097/10000000000 : ℝ)*x 0 + (5094420329/10000000000 : ℝ)*x 1 + (3120858599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4030660097/10000000000 : ℝ)^5431 ≤ (32634902998331/100000000000000 : ℝ)^4407 := by
    have hnat : (4030660097 : ℕ)^5431*100000000000000^4407 ≤ 32634902998331^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030660097 10000000000 32634902998331 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5094420329/10000000000 : ℝ)^5431 ≤ (21777399597637/50000000000000 : ℝ)^4407 := by
    have hnat : (5094420329 : ℕ)^5431*50000000000000^4407 ≤ 21777399597637^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5094420329 10000000000 21777399597637 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3120858599/10000000000 : ℝ)^5431 ≤ (23810297795679/100000000000000 : ℝ)^4407 := by
    have hnat : (3120858599 : ℕ)^5431*100000000000000^4407 ≤ 23810297795679^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3120858599 10000000000 23810297795679 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4030660097/10000000000 : ℝ), (5094420329/10000000000 : ℝ), (3120858599/10000000000 : ℝ)] ![(32634902998331/100000000000000 : ℝ), (21777399597637/50000000000000 : ℝ), (23810297795679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4030660097/10000000000 : ℝ)|^5431 ≤ (32634902998331/100000000000000 : ℝ)^4407
        have hw : |(4030660097/10000000000 : ℝ)|=(4030660097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5094420329/10000000000 : ℝ)|^5431 ≤ (21777399597637/50000000000000 : ℝ)^4407
        have hw : |(5094420329/10000000000 : ℝ)|=(5094420329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3120858599/10000000000 : ℝ)|^5431 ≤ (23810297795679/100000000000000 : ℝ)^4407
        have hw : |(3120858599/10000000000 : ℝ)|=(3120858599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1726_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100131861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3247/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4273/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5423/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5423 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5423*1^1024 ≤ 0^1024*1^5423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5423/1024 : ℝ) ≤ (78081856346213921/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5423 ≤ (78081856346213921/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5423*10000000000000000000^1024 ≤ 78081856346213921^1024*5^5423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 78081856346213921 10000000000000000000 5423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (78081856346213921/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5423/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5423 := by
      have hnat : (1 : ℕ)^1024*1^5423 ≤ 1^5423*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10078081856346213921/10000000000000000000 : ℝ) ≤ (10014697362319091/10000000000000000 : ℝ) ^ (5423/1024 : ℝ) := by
    have hpowers : (10078081856346213921/10000000000000000000 : ℝ)^1024 ≤ (10014697362319091/10000000000000000 : ℝ)^5423 := by
      have hnat : (10078081856346213921 : ℕ)^1024*10000000000000000^5423 ≤ 10014697362319091^5423*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10078081856346213921 10000000000000000000 10014697362319091 10000000000000000 1024 5423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014697362319091/10000000000000000 : ℝ)) (X := (10078081856346213921/10000000000000000000 : ℝ)) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5078081856346213921/5000000000000000000 : ℝ) ≤ (5014697362319091/5000000000000000 : ℝ) ^ (5423/1024 : ℝ) := by
    have hpowers : (5078081856346213921/5000000000000000000 : ℝ)^1024 ≤ (5014697362319091/5000000000000000 : ℝ)^5423 := by
      have hnat : (5078081856346213921 : ℕ)^1024*5000000000000000^5423 ≤ 5014697362319091^5423*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5078081856346213921 5000000000000000000 5014697362319091 5000000000000000 1024 5423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014697362319091/5000000000000000 : ℝ)) (X := (5078081856346213921/5000000000000000000 : ℝ)) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14697362319091/4000000000000000 : ℝ)*(0 : ℝ))^(5423/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14697362319091/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(78081856346213921/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14697362319091/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5423/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14697362319091/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10014697362319091/10000000000000000 : ℝ) by norm_num, show 1+(78081856346213921/10000000000000000000 : ℝ)+(0 : ℝ)=(10078081856346213921/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(78081856346213921/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14697362319091/4000000000000000 : ℝ)*(2/5 : ℝ))^(5423/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14697362319091/4000000000000000 : ℝ)*(2/5 : ℝ)=(5014697362319091/5000000000000000 : ℝ) by norm_num, show 1+2*(78081856346213921/10000000000000000000 : ℝ)=(5078081856346213921/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14697362319091/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5423/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14697362319091/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14697362319091/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5423/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14697362319091/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14697362319091/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5423/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14697362319091/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-645392967/5000000000 : ℝ)*X 0 0+(5666974523/10000000000 : ℝ)*X 0 1+(995279143/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1348331077/2500000000 : ℝ)*X 1 0+(-831430419/5000000000 : ℝ)*X 1 1+(4976395083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5393323027/10000000000 : ℝ)*X 2 0+(2488197937/5000000000 : ℝ)*X 2 1+(-1662861501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((31455743/78125000 : ℝ)*X 0 0+(122765701/400000000 : ℝ)*X 0 1+(5144519757/10000000000 : ℝ)*X 0 2+(31455743/78125000 : ℝ)*X 1 0+(122765701/400000000 : ℝ)*X 1 1+(5144519757/10000000000 : ℝ)*X 1 2+(31455743/78125000 : ℝ)*X 2 0+(122765701/400000000 : ℝ)*X 2 1+(5144519757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-646112947/5000000000 : ℝ)*X 0 0+(4993066799/10000000000 : ℝ)*X 0 1+(353110357/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5206730681/10000000000 : ℝ)*X 1 0+(-989490549/10000000000 : ℝ)*X 1 1+(2824882919/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2603365157/5000000000 : ℝ)*X 2 0+(2824882887/5000000000 : ℝ)*X 2 1+(-61843199/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4030660097/10000000000 : ℝ)*X 0 0+(5094420329/10000000000 : ℝ)*X 0 1+(3120858599/10000000000 : ℝ)*X 0 2+(4030660097/10000000000 : ℝ)*X 1 0+(5094420329/10000000000 : ℝ)*X 1 1+(3120858599/10000000000 : ℝ)*X 1 2+(4030660097/10000000000 : ℝ)*X 2 0+(5094420329/10000000000 : ℝ)*X 2 1+(3120858599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (211595431355591926956873/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (111872113/50000000000000 : ℝ)*(base1) + (1777745227/100000000000000 : ℝ)*(base19) + (286761081/20000000000000 : ℝ)*(base23) + (421573761/100000000000000 : ℝ)*(upper3) + (17293909/25000000000000 : ℝ)*(upper5) + (241239565084799/25000000000000 : ℝ)*(major0) + (241239565084799/25000000000000 : ℝ)*(major1) + (241239565084799/25000000000000 : ℝ)*(major2) + (72403435337591/5000000000000 : ℝ)*(sp0) + (289614138928963/20000000000000 : ℝ)*(sp1) + (362017759646159/25000000000000 : ℝ)*(sp2) + (19273651704661/4000000000000 : ℝ)*(sp3) + (249336403/6250000000000 : ℝ)*(sp4) + (2249800349/100000000000000 : ℝ)*(sp7) + (4818437661611/1000000000000 : ℝ)*(f.failure) + (724036236195021/50000000000000 : ℝ)*(f.sum) + (71194758547709/50000000000000000000000000000 : ℝ)*base65 + (507848085797709/100000000000000000000000000000 : ℝ)*base67 + (542188263602291/100000000000000000000000000000 : ℝ)*base70 + (254199664297709/100000000000000000000000000000 : ℝ)*base71 + (208219437797709/50000000000000000000000000000 : ℝ)*base73 + (183785300502291/100000000000000000000000000000 : ℝ)*base76 + (588044649097709/100000000000000000000000000000 : ℝ)*base77 + (933431480597709/100000000000000000000000000000 : ℝ)*base79 + (252464130402291/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (311929/50000000000000000000 : ℝ)*base90 + (311929/50000000000000000000 : ℝ)*base92 + (311929/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (869644329796244426800737/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (999278791/100000000000000 : ℝ)*(base19) + (223384503/25000000000000 : ℝ)*(base23) + (825683/4000000000000 : ℝ)*(upper2) + (175009601/100000000000000 : ℝ)*(upper3) + (16008997/12500000000000 : ℝ)*(upper5) + (1014732610293123/100000000000000 : ℝ)*(major0) + (1014732610293123/100000000000000 : ℝ)*(major1) + (1014732610293123/100000000000000 : ℝ)*(major2) + (2070827503/50000000000000 : ℝ)*(sp1) + (1539923619/50000000000000 : ℝ)*(sp2) + (761383453885049/50000000000000 : ℝ)*(sp4) + (761380883418151/50000000000000 : ℝ)*(sp5) + (1522762934384849/100000000000000 : ℝ)*(sp6) + (506698167875419/100000000000000 : ℝ)*(sp7) + (506698167875419/100000000000000 : ℝ)*(f.failure) + (761383453885049/50000000000000 : ℝ)*(f.sum) + (640995037288807/200000000000000000000000000000 : ℝ)*base66 + (301484907711193/400000000000000000000000000000 : ℝ)*base67 + (604270533888807/400000000000000000000000000000 : ℝ)*base70 + (909056692288807/400000000000000000000000000000 : ℝ)*base72 + (428226963911193/200000000000000000000000000000 : ℝ)*base73 + (1267993253088807/400000000000000000000000000000 : ℝ)*base76 + (2285334493088807/400000000000000000000000000000 : ℝ)*base78 + (1262146226688807/400000000000000000000000000000 : ℝ)*base80 + (475171936488807/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (29375241/5000000000000000000000 : ℝ)*base90 + (29375241/5000000000000000000000 : ℝ)*base92 + (29375241/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1726_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100131861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3247/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4273/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1726_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1726_s1_0 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-338437631/2500000000 : ℝ)*x 0 + (5470585289/10000000000 : ℝ)*x 1 + (2565576713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338437631/2500000000 : ℝ)^5431 ≤ (8506384876069/100000000000000 : ℝ)^4407 := by
    have hnat : (338437631 : ℕ)^5431*100000000000000^4407 ≤ 8506384876069^4407*2500000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338437631 2500000000 8506384876069 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470585289/10000000000 : ℝ)^5431 ≤ (11887867599137/25000000000000 : ℝ)^4407 := by
    have hnat : (5470585289 : ℕ)^5431*25000000000000^4407 ≤ 11887867599137^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470585289 10000000000 11887867599137 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2565576713/5000000000 : ℝ)^5431 ≤ (21971072353303/50000000000000 : ℝ)^4407 := by
    have hnat : (2565576713 : ℕ)^5431*50000000000000^4407 ≤ 21971072353303^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565576713 5000000000 21971072353303 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-338437631/2500000000 : ℝ), (5470585289/10000000000 : ℝ), (2565576713/5000000000 : ℝ)] ![(8506384876069/100000000000000 : ℝ), (11887867599137/25000000000000 : ℝ), (21971072353303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-338437631/2500000000 : ℝ)|^5431 ≤ (8506384876069/100000000000000 : ℝ)^4407
        have hw : |(-338437631/2500000000 : ℝ)|=(338437631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470585289/10000000000 : ℝ)|^5431 ≤ (11887867599137/25000000000000 : ℝ)^4407
        have hw : |(5470585289/10000000000 : ℝ)|=(5470585289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2565576713/5000000000 : ℝ)|^5431 ≤ (21971072353303/50000000000000 : ℝ)^4407
        have hw : |(2565576713/5000000000 : ℝ)|=(2565576713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s1_1 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068205207/2000000000 : ℝ)*x 0 + (-764949543/5000000000 : ℝ)*x 1 + (5131152483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068205207/2000000000 : ℝ)^5431 ≤ (9233497053367/20000000000000 : ℝ)^4407 := by
    have hnat : (1068205207 : ℕ)^5431*20000000000000^4407 ≤ 9233497053367^4407*2000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068205207 2000000000 9233497053367 20000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (764949543/5000000000 : ℝ)^5431 ≤ (4945189979657/50000000000000 : ℝ)^4407 := by
    have hnat : (764949543 : ℕ)^5431*50000000000000^4407 ≤ 4945189979657^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764949543 5000000000 4945189979657 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5131152483/10000000000 : ℝ)^5431 ≤ (43942134754507/100000000000000 : ℝ)^4407 := by
    have hnat : (5131152483 : ℕ)^5431*100000000000000^4407 ≤ 43942134754507^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131152483 10000000000 43942134754507 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068205207/2000000000 : ℝ), (-764949543/5000000000 : ℝ), (5131152483/10000000000 : ℝ)] ![(9233497053367/20000000000000 : ℝ), (4945189979657/50000000000000 : ℝ), (43942134754507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068205207/2000000000 : ℝ)|^5431 ≤ (9233497053367/20000000000000 : ℝ)^4407
        have hw : |(1068205207/2000000000 : ℝ)|=(1068205207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-764949543/5000000000 : ℝ)|^5431 ≤ (4945189979657/50000000000000 : ℝ)^4407
        have hw : |(-764949543/5000000000 : ℝ)|=(764949543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5131152483/10000000000 : ℝ)|^5431 ≤ (43942134754507/100000000000000 : ℝ)^4407
        have hw : |(5131152483/10000000000 : ℝ)|=(5131152483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s1_2 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1335256189/2500000000 : ℝ)*x 0 + (5131153331/10000000000 : ℝ)*x 1 + (-764949837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335256189/2500000000 : ℝ)^5431 ≤ (4616747164239/10000000000000 : ℝ)^4407 := by
    have hnat : (1335256189 : ℕ)^5431*10000000000000^4407 ≤ 4616747164239^4407*2500000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335256189 2500000000 4616747164239 10000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5131153331/10000000000 : ℝ)^5431 ≤ (43942143704009/100000000000000 : ℝ)^4407 := by
    have hnat : (5131153331 : ℕ)^5431*100000000000000^4407 ≤ 43942143704009^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131153331 10000000000 43942143704009 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (764949837/5000000000 : ℝ)^5431 ≤ (4945192321913/50000000000000 : ℝ)^4407 := by
    have hnat : (764949837 : ℕ)^5431*50000000000000^4407 ≤ 4945192321913^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764949837 5000000000 4945192321913 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1335256189/2500000000 : ℝ), (5131153331/10000000000 : ℝ), (-764949837/5000000000 : ℝ)] ![(4616747164239/10000000000000 : ℝ), (43942143704009/100000000000000 : ℝ), (4945192321913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1335256189/2500000000 : ℝ)|^5431 ≤ (4616747164239/10000000000000 : ℝ)^4407
        have hw : |(1335256189/2500000000 : ℝ)|=(1335256189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5131153331/10000000000 : ℝ)|^5431 ≤ (43942143704009/100000000000000 : ℝ)^4407
        have hw : |(5131153331/10000000000 : ℝ)|=(5131153331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-764949837/5000000000 : ℝ)|^5431 ≤ (4945192321913/50000000000000 : ℝ)^4407
        have hw : |(-764949837/5000000000 : ℝ)|=(764949837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s1_3 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653233/1600000 : ℝ)*x 0 + (3591996369/10000000000 : ℝ)*x 1 + (576509633/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653233/1600000 : ℝ)^5431 ≤ (4144374412439/12500000000000 : ℝ)^4407 := by
    have hnat : (653233 : ℕ)^5431*12500000000000^4407 ≤ 4144374412439^4407*1600000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653233 1600000 4144374412439 12500000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3591996369/10000000000 : ℝ)^5431 ≤ (7078721176973/25000000000000 : ℝ)^4407 := by
    have hnat : (3591996369 : ℕ)^5431*25000000000000^4407 ≤ 7078721176973^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3591996369 10000000000 7078721176973 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (576509633/1250000000 : ℝ)^5431 ≤ (19265059987101/50000000000000 : ℝ)^4407 := by
    have hnat : (576509633 : ℕ)^5431*50000000000000^4407 ≤ 19265059987101^4407*1250000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576509633 1250000000 19265059987101 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653233/1600000 : ℝ), (3591996369/10000000000 : ℝ), (576509633/1250000000 : ℝ)] ![(4144374412439/12500000000000 : ℝ), (7078721176973/25000000000000 : ℝ), (19265059987101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653233/1600000 : ℝ)|^5431 ≤ (4144374412439/12500000000000 : ℝ)^4407
        have hw : |(653233/1600000 : ℝ)|=(653233/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3591996369/10000000000 : ℝ)|^5431 ≤ (7078721176973/25000000000000 : ℝ)^4407
        have hw : |(3591996369/10000000000 : ℝ)|=(3591996369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(576509633/1250000000 : ℝ)|^5431 ≤ (19265059987101/50000000000000 : ℝ)^4407
        have hw : |(576509633/1250000000 : ℝ)|=(576509633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s1_4 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-676960491/5000000000 : ℝ)*x 0 + (641899371/1250000000 : ℝ)*x 1 + (5466479507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676960491/5000000000 : ℝ)^5431 ≤ (2126926213663/25000000000000 : ℝ)^4407 := by
    have hnat : (676960491 : ℕ)^5431*25000000000000^4407 ≤ 2126926213663^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676960491 5000000000 2126926213663 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641899371/1250000000 : ℝ)^5431 ≤ (68726252593/156250000000 : ℝ)^4407 := by
    have hnat : (641899371 : ℕ)^5431*156250000000^4407 ≤ 68726252593^4407*1250000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641899371 1250000000 68726252593 156250000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466479507/10000000000 : ℝ)^5431 ≤ (23753746732719/50000000000000 : ℝ)^4407 := by
    have hnat : (5466479507 : ℕ)^5431*50000000000000^4407 ≤ 23753746732719^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466479507 10000000000 23753746732719 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-676960491/5000000000 : ℝ), (641899371/1250000000 : ℝ), (5466479507/10000000000 : ℝ)] ![(2126926213663/25000000000000 : ℝ), (68726252593/156250000000 : ℝ), (23753746732719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-676960491/5000000000 : ℝ)|^5431 ≤ (2126926213663/25000000000000 : ℝ)^4407
        have hw : |(-676960491/5000000000 : ℝ)|=(676960491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641899371/1250000000 : ℝ)|^5431 ≤ (68726252593/156250000000 : ℝ)^4407
        have hw : |(641899371/1250000000 : ℝ)|=(641899371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466479507/10000000000 : ℝ)|^5431 ≤ (23753746732719/50000000000000 : ℝ)^4407
        have hw : |(5466479507/10000000000 : ℝ)|=(5466479507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s1_5 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164067179/312500000 : ℝ)*x 0 + (-1194572969/10000000000 : ℝ)*x 1 + (546647969/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164067179/312500000 : ℝ)^5431 ≤ (22600677342351/50000000000000 : ℝ)^4407 := by
    have hnat : (164067179 : ℕ)^5431*50000000000000^4407 ≤ 22600677342351^4407*312500000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164067179 312500000 22600677342351 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1194572969/10000000000 : ℝ)^5431 ≤ (7291149867151/100000000000000 : ℝ)^4407 := by
    have hnat : (1194572969 : ℕ)^5431*100000000000000^4407 ≤ 7291149867151^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194572969 10000000000 7291149867151 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546647969/1000000000 : ℝ)^5431 ≤ (1484609232043/3125000000000 : ℝ)^4407 := by
    have hnat : (546647969 : ℕ)^5431*3125000000000^4407 ≤ 1484609232043^4407*1000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546647969 1000000000 1484609232043 3125000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164067179/312500000 : ℝ), (-1194572969/10000000000 : ℝ), (546647969/1000000000 : ℝ)] ![(22600677342351/50000000000000 : ℝ), (7291149867151/100000000000000 : ℝ), (1484609232043/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164067179/312500000 : ℝ)|^5431 ≤ (22600677342351/50000000000000 : ℝ)^4407
        have hw : |(164067179/312500000 : ℝ)|=(164067179/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1194572969/10000000000 : ℝ)|^5431 ≤ (7291149867151/100000000000000 : ℝ)^4407
        have hw : |(-1194572969/10000000000 : ℝ)|=(1194572969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546647969/1000000000 : ℝ)|^5431 ≤ (1484609232043/3125000000000 : ℝ)^4407
        have hw : |(546647969/1000000000 : ℝ)|=(546647969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s1_6 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625074761/5000000000 : ℝ)*x 0 + (2733239933/5000000000 : ℝ)*x 1 + (-1194573009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625074761/5000000000 : ℝ)^5431 ≤ (11300338124759/25000000000000 : ℝ)^4407 := by
    have hnat : (2625074761 : ℕ)^5431*25000000000000^4407 ≤ 11300338124759^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625074761 5000000000 11300338124759 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733239933/5000000000 : ℝ)^5431 ≤ (47507497310343/100000000000000 : ℝ)^4407 := by
    have hnat : (2733239933 : ℕ)^5431*100000000000000^4407 ≤ 47507497310343^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733239933 5000000000 47507497310343 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194573009/10000000000 : ℝ)^5431 ≤ (7291150168021/100000000000000 : ℝ)^4407 := by
    have hnat : (1194573009 : ℕ)^5431*100000000000000^4407 ≤ 7291150168021^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194573009 10000000000 7291150168021 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625074761/5000000000 : ℝ), (2733239933/5000000000 : ℝ), (-1194573009/10000000000 : ℝ)] ![(11300338124759/25000000000000 : ℝ), (47507497310343/100000000000000 : ℝ), (7291150168021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625074761/5000000000 : ℝ)|^5431 ≤ (11300338124759/25000000000000 : ℝ)^4407
        have hw : |(2625074761/5000000000 : ℝ)|=(2625074761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733239933/5000000000 : ℝ)|^5431 ≤ (47507497310343/100000000000000 : ℝ)^4407
        have hw : |(2733239933/5000000000 : ℝ)|=(2733239933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1194573009/10000000000 : ℝ)|^5431 ≤ (7291150168021/100000000000000 : ℝ)^4407
        have hw : |(-1194573009/10000000000 : ℝ)|=(1194573009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s1_7 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4083216953/10000000000 : ℝ)*x 0 + (4599933463/10000000000 : ℝ)*x 1 + (720866239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4083216953/10000000000 : ℝ)^5431 ≤ (33160106375167/100000000000000 : ℝ)^4407 := by
    have hnat : (4083216953 : ℕ)^5431*100000000000000^4407 ≤ 33160106375167^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4083216953 10000000000 33160106375167 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4599933463/10000000000 : ℝ)^5431 ≤ (19202567891043/50000000000000 : ℝ)^4407 := by
    have hnat : (4599933463 : ℕ)^5431*50000000000000^4407 ≤ 19202567891043^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4599933463 10000000000 19202567891043 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (720866239/2000000000 : ℝ)^5431 ≤ (14217378907993/50000000000000 : ℝ)^4407 := by
    have hnat : (720866239 : ℕ)^5431*50000000000000^4407 ≤ 14217378907993^4407*2000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720866239 2000000000 14217378907993 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4083216953/10000000000 : ℝ), (4599933463/10000000000 : ℝ), (720866239/2000000000 : ℝ)] ![(33160106375167/100000000000000 : ℝ), (19202567891043/50000000000000 : ℝ), (14217378907993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4083216953/10000000000 : ℝ)|^5431 ≤ (33160106375167/100000000000000 : ℝ)^4407
        have hw : |(4083216953/10000000000 : ℝ)|=(4083216953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4599933463/10000000000 : ℝ)|^5431 ≤ (19202567891043/50000000000000 : ℝ)^4407
        have hw : |(4599933463/10000000000 : ℝ)|=(4599933463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(720866239/2000000000 : ℝ)|^5431 ≤ (14217378907993/50000000000000 : ℝ)^4407
        have hw : |(720866239/2000000000 : ℝ)|=(720866239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1726_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100131861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4273/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3247/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1987/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17201/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4273/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3247/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4273/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3247/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4273/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3247/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4273/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3247/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4273/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3247/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4273/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3247/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3247/50000 : ℝ) ^ (5423/1024 : ℝ) ≤ (1285658633309/2500000000000000000 : ℝ) := by
    have hpowers : (3247/50000 : ℝ)^5423 ≤ (1285658633309/2500000000000000000 : ℝ)^1024 := by
      have hnat : (3247 : ℕ)^5423*2500000000000000000^1024 ≤ 1285658633309^1024*50000^5423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3247 50000 1285658633309 2500000000000000000 5423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3247/50000 : ℝ)) (X := (1285658633309/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4273/20000 : ℝ) ^ (5423/1024 : ℝ) ≤ (7048790924103119/25000000000000000000 : ℝ) := by
    have hpowers : (4273/20000 : ℝ)^5423 ≤ (7048790924103119/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4273 : ℕ)^5423*25000000000000000000^1024 ≤ 7048790924103119^1024*20000^5423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4273 20000 7048790924103119 25000000000000000000 5423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4273/20000 : ℝ)) (X := (7048790924103119/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250001285658633309/1250000000000000000 : ℝ) ≤ (5000000971059481/5000000000000000 : ℝ) ^ (5423/1024 : ℝ) := by
    have hpowers : (1250001285658633309/1250000000000000000 : ℝ)^1024 ≤ (5000000971059481/5000000000000000 : ℝ)^5423 := by
      have hnat : (1250001285658633309 : ℕ)^1024*5000000000000000^5423 ≤ 5000000971059481^5423*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250001285658633309 1250000000000000000 5000000971059481 5000000000000000 1024 5423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000971059481/5000000000000000 : ℝ)) (X := (1250001285658633309/1250000000000000000 : ℝ)) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25007061647510436209/25000000000000000000 : ℝ) ≤ (5000266653098317/5000000000000000 : ℝ) ^ (5423/1024 : ℝ) := by
    have hpowers : (25007061647510436209/25000000000000000000 : ℝ)^1024 ≤ (5000266653098317/5000000000000000 : ℝ)^5423 := by
      have hnat : (25007061647510436209 : ℕ)^1024*5000000000000000^5423 ≤ 5000266653098317^5423*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007061647510436209 25000000000000000000 5000266653098317 5000000000000000 1024 5423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000266653098317/5000000000000000 : ℝ)) (X := (25007061647510436209/25000000000000000000 : ℝ)) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507048790924103119/12500000000000000000 : ℝ) ≤ (5000532335137153/5000000000000000 : ℝ) ^ (5423/1024 : ℝ) := by
    have hpowers : (12507048790924103119/12500000000000000000 : ℝ)^1024 ≤ (5000532335137153/5000000000000000 : ℝ)^5423 := by
      have hnat : (12507048790924103119 : ℕ)^1024*5000000000000000^5423 ≤ 5000532335137153^5423*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507048790924103119 12500000000000000000 5000532335137153 5000000000000000 1024 5423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000532335137153/5000000000000000 : ℝ)) (X := (12507048790924103119/12500000000000000000 : ℝ)) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1285658633309/2500000000000000000 : ℝ) ≤ ((24783854587435046661/24785000000000000000 : ℝ)+2*(22140169903/61962500000000 : ℝ)*(3247/50000 : ℝ))^(5423/1024 : ℝ) := by
    rw [show (24783854587435046661/24785000000000000000 : ℝ)+2*(22140169903/61962500000000 : ℝ)*(3247/50000 : ℝ)=(5000000971059481/5000000000000000 : ℝ) by norm_num, show 1+2*(1285658633309/2500000000000000000 : ℝ)=(1250001285658633309/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7048790924103119/25000000000000000000 : ℝ)+(1285658633309/2500000000000000000 : ℝ) ≤ ((24783854587435046661/24785000000000000000 : ℝ)+(22140169903/61962500000000 : ℝ)*((4273/20000 : ℝ)+(3247/50000 : ℝ)))^(5423/1024 : ℝ) := by
    rw [show (24783854587435046661/24785000000000000000 : ℝ)+(22140169903/61962500000000 : ℝ)*((4273/20000 : ℝ)+(3247/50000 : ℝ))=(5000266653098317/5000000000000000 : ℝ) by norm_num, show 1+(7048790924103119/25000000000000000000 : ℝ)+(1285658633309/2500000000000000000 : ℝ)=(25007061647510436209/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7048790924103119/25000000000000000000 : ℝ) ≤ ((24783854587435046661/24785000000000000000 : ℝ)+2*(22140169903/61962500000000 : ℝ)*(4273/20000 : ℝ))^(5423/1024 : ℝ) := by
    rw [show (24783854587435046661/24785000000000000000 : ℝ)+2*(22140169903/61962500000000 : ℝ)*(4273/20000 : ℝ)=(5000532335137153/5000000000000000 : ℝ) by norm_num, show 1+2*(7048790924103119/25000000000000000000 : ℝ)=(12507048790924103119/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24783854587435046661/24785000000000000000 : ℝ)*(X 1 0+X 2 0)+(22140169903/61962500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5423/1024 : ℝ)) (lo := (3247/50000 : ℝ)) (hi := (4273/20000 : ℝ)) (c := (24783854587435046661/24785000000000000000 : ℝ)) (alpha := (22140169903/61962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24783854587435046661/24785000000000000000 : ℝ)*(X 0 1+X 2 1)+(22140169903/61962500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5423/1024 : ℝ)) (lo := (3247/50000 : ℝ)) (hi := (4273/20000 : ℝ)) (c := (24783854587435046661/24785000000000000000 : ℝ)) (alpha := (22140169903/61962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24783854587435046661/24785000000000000000 : ℝ)*(X 0 2+X 1 2)+(22140169903/61962500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5423/1024 : ℝ)) (lo := (3247/50000 : ℝ)) (hi := (4273/20000 : ℝ)) (c := (24783854587435046661/24785000000000000000 : ℝ)) (alpha := (22140169903/61962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-338437631/2500000000 : ℝ)*X 0 0+(5470585289/10000000000 : ℝ)*X 0 1+(2565576713/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068205207/2000000000 : ℝ)*X 1 0+(-764949543/5000000000 : ℝ)*X 1 1+(5131152483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1335256189/2500000000 : ℝ)*X 2 0+(5131153331/10000000000 : ℝ)*X 2 1+(-764949837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((653233/1600000 : ℝ)*X 0 0+(3591996369/10000000000 : ℝ)*X 0 1+(576509633/1250000000 : ℝ)*X 0 2+(653233/1600000 : ℝ)*X 1 0+(3591996369/10000000000 : ℝ)*X 1 1+(576509633/1250000000 : ℝ)*X 1 2+(653233/1600000 : ℝ)*X 2 0+(3591996369/10000000000 : ℝ)*X 2 1+(576509633/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-676960491/5000000000 : ℝ)*X 0 0+(641899371/1250000000 : ℝ)*X 0 1+(5466479507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((164067179/312500000 : ℝ)*X 1 0+(-1194572969/10000000000 : ℝ)*X 1 1+(546647969/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2625074761/5000000000 : ℝ)*X 2 0+(2733239933/5000000000 : ℝ)*X 2 1+(-1194573009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4083216953/10000000000 : ℝ)*X 0 0+(4599933463/10000000000 : ℝ)*X 0 1+(720866239/2000000000 : ℝ)*X 0 2+(4083216953/10000000000 : ℝ)*X 1 0+(4599933463/10000000000 : ℝ)*X 1 1+(720866239/2000000000 : ℝ)*X 1 2+(4083216953/10000000000 : ℝ)*X 2 0+(4599933463/10000000000 : ℝ)*X 2 1+(720866239/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4074808711253411110458569649/619625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125525593/12500000000000 : ℝ)*(base19) + (10519809/100000000000000 : ℝ)*(base23) + (203030741/100000000000000 : ℝ)*(lower2) + (56902967/50000000000000 : ℝ)*(lower4) + (40629423/50000000000000 : ℝ)*(lower5) + (1963214611644097/100000000000000 : ℝ)*(major0) + (1963214611644097/100000000000000 : ℝ)*(major1) + (1963214611644097/100000000000000 : ℝ)*(major2) + (2946108055198357/100000000000000 : ℝ)*(sp0) + (1473056673378907/50000000000000 : ℝ)*(sp1) + (1473053610567283/50000000000000 : ℝ)*(sp2) + (980314653117301/100000000000000 : ℝ)*(sp3) + (31478821/500000000000 : ℝ)*(sp4) + (3559654091/50000000000000 : ℝ)*(sp6) + (980314653117301/100000000000000 : ℝ)*(f.failure) + (2946114350962557/100000000000000 : ℝ)*(f.sum) + (148530825786929/12392500000000000000000000000 : ℝ)*base65 + (22190634525759610117/2478500000000000000000000000000000 : ℝ)*base67 + (20342023232195610117/2478500000000000000000000000000000 : ℝ)*base69 + (22375721723066610117/2478500000000000000000000000000000 : ℝ)*base71 + (122019465719703/24785000000000000000000000000 : ℝ)*base73 + (5611296261684389883/2478500000000000000000000000000000 : ℝ)*base76 + (35517676972381610117/2478500000000000000000000000000000 : ℝ)*base77 + (28767366037737110117/2478500000000000000000000000000000 : ℝ)*base79 + (8623366211871/12392500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (49572839/5000000000000000000000 : ℝ)*base90 + (49572839/5000000000000000000000 : ℝ)*base92 + (49572839/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3679317370762578845504618301/309812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (549237577/50000000000000 : ℝ)*(base19) + (1419347381/100000000000000 : ℝ)*(base23) + (243137877/100000000000000 : ℝ)*(upper3) + (23778497/12500000000000 : ℝ)*(lower4) + (67023771/50000000000000 : ℝ)*(upper5) + (502870726624249/25000000000000 : ℝ)*(major0) + (502870726624249/25000000000000 : ℝ)*(major1) + (502870726624249/25000000000000 : ℝ)*(major2) + (9247609327/100000000000000 : ℝ)*(sp1) + (13695224541/100000000000000 : ℝ)*(sp2) + (3018548398205853/100000000000000 : ℝ)*(sp4) + (754634513030343/25000000000000 : ℝ)*(sp5) + (754633320908483/25000000000000 : ℝ)*(sp6) + (125552127365397/12500000000000 : ℝ)*(sp7) + (125552127365397/12500000000000 : ℝ)*(f.failure) + (3018548398205853/100000000000000 : ℝ)*(f.sum) + (49007766641867/12392500000000000000000000000 : ℝ)*base65 + (1356712384250117411/619625000000000000000000000000000 : ℝ)*base68 + (1255554636780492411/619625000000000000000000000000000 : ℝ)*base70 + (266501898966242411/619625000000000000000000000000000 : ℝ)*base72 + (26305018734587/12392500000000000000000000000 : ℝ)*base73 + (1572176288849242411/619625000000000000000000000000000 : ℝ)*base76 + (2080703323806617411/619625000000000000000000000000000 : ℝ)*base78 + (9030000590675492411/619625000000000000000000000000000 : ℝ)*base80 + (14148417407587/12392500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3613817/625000000000000000000 : ℝ)*base89 + (3613817/625000000000000000000 : ℝ)*base91 + (3613817/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1726_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100131861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4273/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3247/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1987/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17201/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1726_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1726_s2_0 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1356226027/10000000000 : ℝ)*x 0 + (2730155151/5000000000 : ℝ)*x 1 + (256988089/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1356226027/10000000000 : ℝ)^5431 ≤ (1705111652383/20000000000000 : ℝ)^4407 := by
    have hnat : (1356226027 : ℕ)^5431*20000000000000^4407 ≤ 1705111652383^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356226027 10000000000 1705111652383 20000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730155151/5000000000 : ℝ)^5431 ≤ (47441429690661/100000000000000 : ℝ)^4407 := by
    have hnat : (2730155151 : ℕ)^5431*100000000000000^4407 ≤ 47441429690661^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730155151 5000000000 47441429690661 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256988089/500000000 : ℝ)^5431 ≤ (5504126503423/12500000000000 : ℝ)^4407 := by
    have hnat : (256988089 : ℕ)^5431*12500000000000^4407 ≤ 5504126503423^4407*500000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256988089 500000000 5504126503423 12500000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1356226027/10000000000 : ℝ), (2730155151/5000000000 : ℝ), (256988089/500000000 : ℝ)] ![(1705111652383/20000000000000 : ℝ), (47441429690661/100000000000000 : ℝ), (5504126503423/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1356226027/10000000000 : ℝ)|^5431 ≤ (1705111652383/20000000000000 : ℝ)^4407
        have hw : |(-1356226027/10000000000 : ℝ)|=(1356226027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730155151/5000000000 : ℝ)|^5431 ≤ (47441429690661/100000000000000 : ℝ)^4407
        have hw : |(2730155151/5000000000 : ℝ)|=(2730155151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(256988089/500000000 : ℝ)|^5431 ≤ (5504126503423/12500000000000 : ℝ)^4407
        have hw : |(256988089/500000000 : ℝ)|=(256988089/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s2_1 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2669110827/5000000000 : ℝ)*x 0 + (-1522237699/10000000000 : ℝ)*x 1 + (5139761397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2669110827/5000000000 : ℝ)^5431 ≤ (46137613645473/100000000000000 : ℝ)^4407 := by
    have hnat : (2669110827 : ℕ)^5431*100000000000000^4407 ≤ 46137613645473^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2669110827 5000000000 46137613645473 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1522237699/10000000000 : ℝ)^5431 ≤ (1965875670511/20000000000000 : ℝ)^4407 := by
    have hnat : (1522237699 : ℕ)^5431*20000000000000^4407 ≤ 1965875670511^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522237699 10000000000 1965875670511 20000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139761397/10000000000 : ℝ)^5431 ≤ (22016503991879/50000000000000 : ℝ)^4407 := by
    have hnat : (5139761397 : ℕ)^5431*50000000000000^4407 ≤ 22016503991879^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139761397 10000000000 22016503991879 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2669110827/5000000000 : ℝ), (-1522237699/10000000000 : ℝ), (5139761397/10000000000 : ℝ)] ![(46137613645473/100000000000000 : ℝ), (1965875670511/20000000000000 : ℝ), (22016503991879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2669110827/5000000000 : ℝ)|^5431 ≤ (46137613645473/100000000000000 : ℝ)^4407
        have hw : |(2669110827/5000000000 : ℝ)|=(2669110827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1522237699/10000000000 : ℝ)|^5431 ≤ (1965875670511/20000000000000 : ℝ)^4407
        have hw : |(-1522237699/10000000000 : ℝ)|=(1522237699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139761397/10000000000 : ℝ)|^5431 ≤ (22016503991879/50000000000000 : ℝ)^4407
        have hw : |(5139761397/10000000000 : ℝ)|=(5139761397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s2_2 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2669110451/5000000000 : ℝ)*x 0 + (5139762583/10000000000 : ℝ)*x 1 + (-1522237133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2669110451/5000000000 : ℝ)^5431 ≤ (46137605635831/100000000000000 : ℝ)^4407 := by
    have hnat : (2669110451 : ℕ)^5431*100000000000000^4407 ≤ 46137605635831^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2669110451 5000000000 46137605635831 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5139762583/10000000000 : ℝ)^5431 ≤ (5504127563159/12500000000000 : ℝ)^4407 := by
    have hnat : (5139762583 : ℕ)^5431*12500000000000^4407 ≤ 5504127563159^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139762583 10000000000 5504127563159 12500000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1522237133/10000000000 : ℝ)^5431 ≤ (2457343462143/25000000000000 : ℝ)^4407 := by
    have hnat : (1522237133 : ℕ)^5431*25000000000000^4407 ≤ 2457343462143^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522237133 10000000000 2457343462143 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2669110451/5000000000 : ℝ), (5139762583/10000000000 : ℝ), (-1522237133/10000000000 : ℝ)] ![(46137605635831/100000000000000 : ℝ), (5504127563159/12500000000000 : ℝ), (2457343462143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2669110451/5000000000 : ℝ)|^5431 ≤ (46137605635831/100000000000000 : ℝ)^4407
        have hw : |(2669110451/5000000000 : ℝ)|=(2669110451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5139762583/10000000000 : ℝ)|^5431 ≤ (5504127563159/12500000000000 : ℝ)^4407
        have hw : |(5139762583/10000000000 : ℝ)|=(5139762583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1522237133/10000000000 : ℝ)|^5431 ≤ (2457343462143/25000000000000 : ℝ)^4407
        have hw : |(-1522237133/10000000000 : ℝ)|=(1522237133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s2_3 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4084634509/10000000000 : ℝ)*x 0 + (3620204991/10000000000 : ℝ)*x 1 + (458354091/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4084634509/10000000000 : ℝ)^5431 ≤ (2073393371437/6250000000000 : ℝ)^4407 := by
    have hnat : (4084634509 : ℕ)^5431*6250000000000^4407 ≤ 2073393371437^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4084634509 10000000000 2073393371437 6250000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3620204991/10000000000 : ℝ)^5431 ≤ (28589163859683/100000000000000 : ℝ)^4407 := by
    have hnat : (3620204991 : ℕ)^5431*100000000000000^4407 ≤ 28589163859683^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3620204991 10000000000 28589163859683 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458354091/1000000000 : ℝ)^5431 ≤ (9559135544431/25000000000000 : ℝ)^4407 := by
    have hnat : (458354091 : ℕ)^5431*25000000000000^4407 ≤ 9559135544431^4407*1000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458354091 1000000000 9559135544431 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4084634509/10000000000 : ℝ), (3620204991/10000000000 : ℝ), (458354091/1000000000 : ℝ)] ![(2073393371437/6250000000000 : ℝ), (28589163859683/100000000000000 : ℝ), (9559135544431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4084634509/10000000000 : ℝ)|^5431 ≤ (2073393371437/6250000000000 : ℝ)^4407
        have hw : |(4084634509/10000000000 : ℝ)|=(4084634509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3620204991/10000000000 : ℝ)|^5431 ≤ (28589163859683/100000000000000 : ℝ)^4407
        have hw : |(3620204991/10000000000 : ℝ)|=(3620204991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(458354091/1000000000 : ℝ)|^5431 ≤ (9559135544431/25000000000000 : ℝ)^4407
        have hw : |(458354091/1000000000 : ℝ)|=(458354091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s2_4 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-678184827/5000000000 : ℝ)*x 0 + (5143367411/10000000000 : ℝ)*x 1 + (545665051/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (678184827/5000000000 : ℝ)^5431 ≤ (8526670938469/100000000000000 : ℝ)^4407 := by
    have hnat : (678184827 : ℕ)^5431*100000000000000^4407 ≤ 8526670938469^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678184827 5000000000 8526670938469 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5143367411/10000000000 : ℝ)^5431 ≤ (22035541274287/50000000000000 : ℝ)^4407 := by
    have hnat : (5143367411 : ℕ)^5431*50000000000000^4407 ≤ 22035541274287^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143367411 10000000000 22035541274287 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545665051/1000000000 : ℝ)^5431 ≤ (47402246502013/100000000000000 : ℝ)^4407 := by
    have hnat : (545665051 : ℕ)^5431*100000000000000^4407 ≤ 47402246502013^4407*1000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545665051 1000000000 47402246502013 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-678184827/5000000000 : ℝ), (5143367411/10000000000 : ℝ), (545665051/1000000000 : ℝ)] ![(8526670938469/100000000000000 : ℝ), (22035541274287/50000000000000 : ℝ), (47402246502013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-678184827/5000000000 : ℝ)|^5431 ≤ (8526670938469/100000000000000 : ℝ)^4407
        have hw : |(-678184827/5000000000 : ℝ)|=(678184827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5143367411/10000000000 : ℝ)|^5431 ≤ (22035541274287/50000000000000 : ℝ)^4407
        have hw : |(5143367411/10000000000 : ℝ)|=(5143367411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545665051/1000000000 : ℝ)|^5431 ≤ (47402246502013/100000000000000 : ℝ)^4407
        have hw : |(545665051/1000000000 : ℝ)|=(545665051/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s2_5 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252422683/10000000000 : ℝ)*x 0 + (-120534793/1000000000 : ℝ)*x 1 + (5456650517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252422683/10000000000 : ℝ)^5431 ≤ (2826592000803/6250000000000 : ℝ)^4407 := by
    have hnat : (5252422683 : ℕ)^5431*6250000000000^4407 ≤ 2826592000803^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252422683 10000000000 2826592000803 6250000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120534793/1000000000 : ℝ)^5431 ≤ (7372281389547/100000000000000 : ℝ)^4407 := by
    have hnat : (120534793 : ℕ)^5431*100000000000000^4407 ≤ 7372281389547^4407*1000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120534793 1000000000 7372281389547 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456650517/10000000000 : ℝ)^5431 ≤ (5925280822119/12500000000000 : ℝ)^4407 := by
    have hnat : (5456650517 : ℕ)^5431*12500000000000^4407 ≤ 5925280822119^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456650517 10000000000 5925280822119 12500000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252422683/10000000000 : ℝ), (-120534793/1000000000 : ℝ), (5456650517/10000000000 : ℝ)] ![(2826592000803/6250000000000 : ℝ), (7372281389547/100000000000000 : ℝ), (5925280822119/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252422683/10000000000 : ℝ)|^5431 ≤ (2826592000803/6250000000000 : ℝ)^4407
        have hw : |(5252422683/10000000000 : ℝ)|=(5252422683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-120534793/1000000000 : ℝ)|^5431 ≤ (7372281389547/100000000000000 : ℝ)^4407
        have hw : |(-120534793/1000000000 : ℝ)|=(120534793/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456650517/10000000000 : ℝ)|^5431 ≤ (5925280822119/12500000000000 : ℝ)^4407
        have hw : |(5456650517/10000000000 : ℝ)|=(5456650517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s2_6 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105048453/200000000 : ℝ)*x 0 + (1364162649/2500000000 : ℝ)*x 1 + (-241069573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105048453/200000000 : ℝ)^5431 ≤ (22612735831341/50000000000000 : ℝ)^4407 := by
    have hnat : (105048453 : ℕ)^5431*50000000000000^4407 ≤ 22612735831341^4407*200000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105048453 200000000 22612735831341 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364162649/2500000000 : ℝ)^5431 ≤ (11850561855673/25000000000000 : ℝ)^4407 := by
    have hnat : (1364162649 : ℕ)^5431*25000000000000^4407 ≤ 11850561855673^4407*2500000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364162649 2500000000 11850561855673 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241069573/2000000000 : ℝ)^5431 ≤ (737228089961/10000000000000 : ℝ)^4407 := by
    have hnat : (241069573 : ℕ)^5431*10000000000000^4407 ≤ 737228089961^4407*2000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241069573 2000000000 737228089961 10000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105048453/200000000 : ℝ), (1364162649/2500000000 : ℝ), (-241069573/2000000000 : ℝ)] ![(22612735831341/50000000000000 : ℝ), (11850561855673/25000000000000 : ℝ), (737228089961/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105048453/200000000 : ℝ)|^5431 ≤ (22612735831341/50000000000000 : ℝ)^4407
        have hw : |(105048453/200000000 : ℝ)|=(105048453/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364162649/2500000000 : ℝ)|^5431 ≤ (11850561855673/25000000000000 : ℝ)^4407
        have hw : |(1364162649/2500000000 : ℝ)|=(1364162649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-241069573/2000000000 : ℝ)|^5431 ≤ (737228089961/10000000000000 : ℝ)^4407
        have hw : |(-241069573/2000000000 : ℝ)|=(241069573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s2_7 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4085064447/10000000000 : ℝ)*x 0 + (2286352329/5000000000 : ℝ)*x 1 + (1815601353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4085064447/10000000000 : ℝ)^5431 ≤ (16589298595523/50000000000000 : ℝ)^4407 := by
    have hnat : (4085064447 : ℕ)^5431*50000000000000^4407 ≤ 16589298595523^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4085064447 10000000000 16589298595523 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2286352329/5000000000 : ℝ)^5431 ≤ (7625034140469/20000000000000 : ℝ)^4407 := by
    have hnat : (2286352329 : ℕ)^5431*20000000000000^4407 ≤ 7625034140469^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286352329 5000000000 7625034140469 20000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1815601353/5000000000 : ℝ)^5431 ≤ (28696232092983/100000000000000 : ℝ)^4407 := by
    have hnat : (1815601353 : ℕ)^5431*100000000000000^4407 ≤ 28696232092983^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815601353 5000000000 28696232092983 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4085064447/10000000000 : ℝ), (2286352329/5000000000 : ℝ), (1815601353/5000000000 : ℝ)] ![(16589298595523/50000000000000 : ℝ), (7625034140469/20000000000000 : ℝ), (28696232092983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4085064447/10000000000 : ℝ)|^5431 ≤ (16589298595523/50000000000000 : ℝ)^4407
        have hw : |(4085064447/10000000000 : ℝ)|=(4085064447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2286352329/5000000000 : ℝ)|^5431 ≤ (7625034140469/20000000000000 : ℝ)^4407
        have hw : |(2286352329/5000000000 : ℝ)|=(2286352329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1815601353/5000000000 : ℝ)|^5431 ≤ (28696232092983/100000000000000 : ℝ)^4407
        have hw : |(1815601353/5000000000 : ℝ)|=(1815601353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1726_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100131861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17201/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1987/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10123/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2123/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17201/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1987/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17201/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1987/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17201/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1987/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17201/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1987/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17201/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1987/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17201/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1987/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (1987/20000 : ℝ) ^ (5423/1024 : ℝ) ≤ (6109601867211/1250000000000000000 : ℝ) := by
    have hpowers : (1987/20000 : ℝ)^5423 ≤ (6109601867211/1250000000000000000 : ℝ)^1024 := by
      have hnat : (1987 : ℕ)^5423*1250000000000000000^1024 ≤ 6109601867211^1024*20000^5423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1987 20000 6109601867211 1250000000000000000 5423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1987/20000 : ℝ)) (X := (6109601867211/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17201/100000 : ℝ) ^ (5423/1024 : ℝ) ≤ (8944787186075641/100000000000000000000 : ℝ) := by
    have hpowers : (17201/100000 : ℝ)^5423 ≤ (8944787186075641/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17201 : ℕ)^5423*100000000000000000000^1024 ≤ 8944787186075641^1024*100000^5423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17201 100000 8944787186075641 100000000000000000000 5423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17201/100000 : ℝ)) (X := (8944787186075641/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (625006109601867211/625000000000000000 : ℝ) ≤ (10000018458292481/10000000000000000 : ℝ) ^ (5423/1024 : ℝ) := by
    have hpowers : (625006109601867211/625000000000000000 : ℝ)^1024 ≤ (10000018458292481/10000000000000000 : ℝ)^5423 := by
      have hnat : (625006109601867211 : ℕ)^1024*10000000000000000^5423 ≤ 10000018458292481^5423*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625006109601867211 625000000000000000 10000018458292481 10000000000000000 1024 5423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000018458292481/10000000000000000 : ℝ)) (X := (625006109601867211/625000000000000000 : ℝ)) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100009433555335452521/100000000000000000000 : ℝ) ≤ (10000178122645803/10000000000000000 : ℝ) ^ (5423/1024 : ℝ) := by
    have hpowers : (100009433555335452521/100000000000000000000 : ℝ)^1024 ≤ (10000178122645803/10000000000000000 : ℝ)^5423 := by
      have hnat : (100009433555335452521 : ℕ)^1024*10000000000000000^5423 ≤ 10000178122645803^5423*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100009433555335452521 100000000000000000000 10000178122645803 10000000000000000 1024 5423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000178122645803/10000000000000000 : ℝ)) (X := (100009433555335452521/100000000000000000000 : ℝ)) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008944787186075641/50000000000000000000 : ℝ) ≤ (80002702295993/80000000000000 : ℝ) ^ (5423/1024 : ℝ) := by
    have hpowers : (50008944787186075641/50000000000000000000 : ℝ)^1024 ≤ (80002702295993/80000000000000 : ℝ)^5423 := by
      have hnat : (50008944787186075641 : ℕ)^1024*80000000000000^5423 ≤ 80002702295993^5423*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008944787186075641 50000000000000000000 80002702295993 80000000000000 1024 5423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80002702295993/80000000000000 : ℝ)) (X := (50008944787186075641/50000000000000000000 : ℝ)) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6109601867211/1250000000000000000 : ℝ) ≤ ((36328480793626329403/36330000000000000000 : ℝ)+2*(79832176661/363300000000000 : ℝ)*(1987/20000 : ℝ))^(5423/1024 : ℝ) := by
    rw [show (36328480793626329403/36330000000000000000 : ℝ)+2*(79832176661/363300000000000 : ℝ)*(1987/20000 : ℝ)=(10000018458292481/10000000000000000 : ℝ) by norm_num, show 1+2*(6109601867211/1250000000000000000 : ℝ)=(625006109601867211/625000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8944787186075641/100000000000000000000 : ℝ)+(6109601867211/1250000000000000000 : ℝ) ≤ ((36328480793626329403/36330000000000000000 : ℝ)+(79832176661/363300000000000 : ℝ)*((17201/100000 : ℝ)+(1987/20000 : ℝ)))^(5423/1024 : ℝ) := by
    rw [show (36328480793626329403/36330000000000000000 : ℝ)+(79832176661/363300000000000 : ℝ)*((17201/100000 : ℝ)+(1987/20000 : ℝ))=(10000178122645803/10000000000000000 : ℝ) by norm_num, show 1+(8944787186075641/100000000000000000000 : ℝ)+(6109601867211/1250000000000000000 : ℝ)=(100009433555335452521/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8944787186075641/100000000000000000000 : ℝ) ≤ ((36328480793626329403/36330000000000000000 : ℝ)+2*(79832176661/363300000000000 : ℝ)*(17201/100000 : ℝ))^(5423/1024 : ℝ) := by
    rw [show (36328480793626329403/36330000000000000000 : ℝ)+2*(79832176661/363300000000000 : ℝ)*(17201/100000 : ℝ)=(80002702295993/80000000000000 : ℝ) by norm_num, show 1+2*(8944787186075641/100000000000000000000 : ℝ)=(50008944787186075641/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36328480793626329403/36330000000000000000 : ℝ)*(X 1 0+X 2 0)+(79832176661/363300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5423/1024 : ℝ)) (lo := (1987/20000 : ℝ)) (hi := (17201/100000 : ℝ)) (c := (36328480793626329403/36330000000000000000 : ℝ)) (alpha := (79832176661/363300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36328480793626329403/36330000000000000000 : ℝ)*(X 0 1+X 2 1)+(79832176661/363300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5423/1024 : ℝ)) (lo := (1987/20000 : ℝ)) (hi := (17201/100000 : ℝ)) (c := (36328480793626329403/36330000000000000000 : ℝ)) (alpha := (79832176661/363300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36328480793626329403/36330000000000000000 : ℝ)*(X 0 2+X 1 2)+(79832176661/363300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5423/1024 : ℝ)) (lo := (1987/20000 : ℝ)) (hi := (17201/100000 : ℝ)) (c := (36328480793626329403/36330000000000000000 : ℝ)) (alpha := (79832176661/363300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1356226027/10000000000 : ℝ)*X 0 0+(2730155151/5000000000 : ℝ)*X 0 1+(256988089/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2669110827/5000000000 : ℝ)*X 1 0+(-1522237699/10000000000 : ℝ)*X 1 1+(5139761397/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2669110451/5000000000 : ℝ)*X 2 0+(5139762583/10000000000 : ℝ)*X 2 1+(-1522237133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4084634509/10000000000 : ℝ)*X 0 0+(3620204991/10000000000 : ℝ)*X 0 1+(458354091/1000000000 : ℝ)*X 0 2+(4084634509/10000000000 : ℝ)*X 1 0+(3620204991/10000000000 : ℝ)*X 1 1+(458354091/1000000000 : ℝ)*X 1 2+(4084634509/10000000000 : ℝ)*X 2 0+(3620204991/10000000000 : ℝ)*X 2 1+(458354091/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-678184827/5000000000 : ℝ)*X 0 0+(5143367411/10000000000 : ℝ)*X 0 1+(545665051/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252422683/10000000000 : ℝ)*X 1 0+(-120534793/1000000000 : ℝ)*X 1 1+(5456650517/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((105048453/200000000 : ℝ)*X 2 0+(1364162649/2500000000 : ℝ)*X 2 1+(-241069573/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4085064447/10000000000 : ℝ)*X 0 0+(2286352329/5000000000 : ℝ)*X 0 1+(1815601353/5000000000 : ℝ)*X 0 2+(4085064447/10000000000 : ℝ)*X 1 0+(2286352329/5000000000 : ℝ)*X 1 1+(1815601353/5000000000 : ℝ)*X 1 2+(4085064447/10000000000 : ℝ)*X 2 0+(2286352329/5000000000 : ℝ)*X 2 1+(1815601353/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (495137111750488935529866543/151375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21535287/4000000000000 : ℝ)*(base21) + (67162343/50000000000000 : ℝ)*(lower2) + (14190247/20000000000000 : ℝ)*(lower4) + (830089/6250000000000 : ℝ)*(upper5) + (1039428091636619/50000000000000 : ℝ)*(major0) + (1039428091636619/50000000000000 : ℝ)*(major1) + (1039428091636619/50000000000000 : ℝ)*(major2) + (1559825627520103/50000000000000 : ℝ)*(sp0) + (1559823742276427/50000000000000 : ℝ)*(sp1) + (779913105716327/25000000000000 : ℝ)*(sp2) + (207611804331021/20000000000000 : ℝ)*(sp3) + (1706207277/100000000000000 : ℝ)*(sp4) + (547669463/10000000000000 : ℝ)*(sp5) + (137306431/50000000000000 : ℝ)*(sp7) + (1038059296267967/100000000000000 : ℝ)*(f.failure) + (779913240311871/25000000000000 : ℝ)*(f.sum) + (126498936340117/18165000000000000000000000000 : ℝ)*base66 + (307071367890702819/605500000000000000000000000000000 : ℝ)*base67 + (3298819158999702819/605500000000000000000000000000000 : ℝ)*base69 + (612766365488202819/605500000000000000000000000000000 : ℝ)*base71 + (94302552223507/18165000000000000000000000000 : ℝ)*base74 + (132012140189297181/605500000000000000000000000000000 : ℝ)*base76 + (5644668146933202819/605500000000000000000000000000000 : ℝ)*base77 + (4831174513113202819/605500000000000000000000000000000 : ℝ)*base79 + (2235950761469/2270625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (9603413/5000000000000000000000 : ℝ)*base90 + (9603413/5000000000000000000000 : ℝ)*base92 + (9603413/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (237916465433884251304883533/43250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195848763/20000000000000 : ℝ)*(base19) + (1062321713/100000000000000 : ℝ)*(base23) + (39854221/25000000000000 : ℝ)*(upper3) + (39169353/100000000000000 : ℝ)*(lower4) + (134083803/100000000000000 : ℝ)*(upper5) + (1063533235154341/50000000000000 : ℝ)*(major0) + (1063533235154341/50000000000000 : ℝ)*(major1) + (1063533235154341/50000000000000 : ℝ)*(major2) + (4539793043/50000000000000 : ℝ)*(sp1) + (10827980703/100000000000000 : ℝ)*(sp2) + (399000007611559/12500000000000 : ℝ)*(sp4) + (797997500515643/25000000000000 : ℝ)*(sp5) + (3191988170590057/100000000000000 : ℝ)*(sp6) + (531066348179797/50000000000000 : ℝ)*(sp7) + (531066348179797/50000000000000 : ℝ)*(f.failure) + (399000007611559/12500000000000 : ℝ)*(f.sum) + (280479607459/648750000000000000000000000 : ℝ)*base65 + (5666226829785163/86500000000000000000000000000000 : ℝ)*base67 + (341061046569785163/86500000000000000000000000000000 : ℝ)*base69 + (147633262448785163/86500000000000000000000000000000 : ℝ)*base71 + (38314855079/10136718750000000000000000 : ℝ)*base74 + (190783632440785163/86500000000000000000000000000000 : ℝ)*base75 + (73380085034785163/86500000000000000000000000000000 : ℝ)*base77 + (449745996621285163/86500000000000000000000000000000 : ℝ)*base79 + (1892546187743/1297500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (13787783/2500000000000000000000 : ℝ)*base90 + (13787783/2500000000000000000000 : ℝ)*base92 + (13787783/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1726_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100131861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17201/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1987/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10123/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2123/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1726_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1726_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100131861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10123/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2123/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1726_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1726_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1726_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100131861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10123/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2123/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1726_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

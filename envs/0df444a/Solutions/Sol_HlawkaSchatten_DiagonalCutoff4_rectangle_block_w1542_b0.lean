-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1542_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:08:03.678903+00:00
-- url     : https://prove2.me/submissions/8396f634-0dae-45ef-8afa-8a8b053e28b1

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
theorem support_rectangle_w1542_s0_0 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1654473023/10000000000 : ℝ)*x 0 + (2945050541/5000000000 : ℝ)*x 1 + (304246347/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1654473023/10000000000 : ℝ)^4581 ≤ (1971310595993/20000000000000 : ℝ)^3557 := by
    have hnat : (1654473023 : ℕ)^4581*20000000000000^3557 ≤ 1971310595993^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1654473023 10000000000 1971310595993 20000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2945050541/5000000000 : ℝ)^4581 ≤ (50576058873853/100000000000000 : ℝ)^3557 := by
    have hnat : (2945050541 : ℕ)^4581*100000000000000^3557 ≤ 50576058873853^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2945050541 5000000000 50576058873853 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (304246347/625000000 : ℝ)^4581 ≤ (39567388131477/100000000000000 : ℝ)^3557 := by
    have hnat : (304246347 : ℕ)^4581*100000000000000^3557 ≤ 39567388131477^3557*625000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304246347 625000000 39567388131477 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1654473023/10000000000 : ℝ), (2945050541/5000000000 : ℝ), (304246347/625000000 : ℝ)] ![(1971310595993/20000000000000 : ℝ), (50576058873853/100000000000000 : ℝ), (39567388131477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1654473023/10000000000 : ℝ)|^4581 ≤ (1971310595993/20000000000000 : ℝ)^3557
        have hw : |(-1654473023/10000000000 : ℝ)|=(1654473023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2945050541/5000000000 : ℝ)|^4581 ≤ (50576058873853/100000000000000 : ℝ)^3557
        have hw : |(2945050541/5000000000 : ℝ)|=(2945050541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(304246347/625000000 : ℝ)|^4581 ≤ (39567388131477/100000000000000 : ℝ)^3557
        have hw : |(304246347/625000000 : ℝ)|=(304246347/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s0_1 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2735741263/5000000000 : ℝ)*x 0 + (-89009593/400000000 : ℝ)*x 1 + (2433970809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2735741263/5000000000 : ℝ)^4581 ≤ (5749365301877/12500000000000 : ℝ)^3557 := by
    have hnat : (2735741263 : ℕ)^4581*12500000000000^3557 ≤ 5749365301877^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735741263 5000000000 5749365301877 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89009593/400000000 : ℝ)^4581 ≤ (7218844376299/50000000000000 : ℝ)^3557 := by
    have hnat : (89009593 : ℕ)^4581*50000000000000^3557 ≤ 7218844376299^3557*400000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89009593 400000000 7218844376299 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2433970809/5000000000 : ℝ)^4581 ≤ (9891847205593/25000000000000 : ℝ)^3557 := by
    have hnat : (2433970809 : ℕ)^4581*25000000000000^3557 ≤ 9891847205593^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2433970809 5000000000 9891847205593 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2735741263/5000000000 : ℝ), (-89009593/400000000 : ℝ), (2433970809/5000000000 : ℝ)] ![(5749365301877/12500000000000 : ℝ), (7218844376299/50000000000000 : ℝ), (9891847205593/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2735741263/5000000000 : ℝ)|^4581 ≤ (5749365301877/12500000000000 : ℝ)^3557
        have hw : |(2735741263/5000000000 : ℝ)|=(2735741263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89009593/400000000 : ℝ)|^4581 ≤ (7218844376299/50000000000000 : ℝ)^3557
        have hw : |(-89009593/400000000 : ℝ)|=(89009593/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2433970809/5000000000 : ℝ)|^4581 ≤ (9891847205593/25000000000000 : ℝ)^3557
        have hw : |(2433970809/5000000000 : ℝ)|=(2433970809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s0_2 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5471482457/10000000000 : ℝ)*x 0 + (973588317/2000000000 : ℝ)*x 1 + (-1112619977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5471482457/10000000000 : ℝ)^4581 ≤ (45994921667999/100000000000000 : ℝ)^3557 := by
    have hnat : (5471482457 : ℕ)^4581*100000000000000^3557 ≤ 45994921667999^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471482457 10000000000 45994921667999 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973588317/2000000000 : ℝ)^4581 ≤ (1582695539077/4000000000000 : ℝ)^3557 := by
    have hnat : (973588317 : ℕ)^4581*4000000000000^3557 ≤ 1582695539077^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973588317 2000000000 1582695539077 4000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112619977/5000000000 : ℝ)^4581 ≤ (14437689830519/100000000000000 : ℝ)^3557 := by
    have hnat : (1112619977 : ℕ)^4581*100000000000000^3557 ≤ 14437689830519^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112619977 5000000000 14437689830519 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5471482457/10000000000 : ℝ), (973588317/2000000000 : ℝ), (-1112619977/5000000000 : ℝ)] ![(45994921667999/100000000000000 : ℝ), (1582695539077/4000000000000 : ℝ), (14437689830519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5471482457/10000000000 : ℝ)|^4581 ≤ (45994921667999/100000000000000 : ℝ)^3557
        have hw : |(5471482457/10000000000 : ℝ)|=(5471482457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(973588317/2000000000 : ℝ)|^4581 ≤ (1582695539077/4000000000000 : ℝ)^3557
        have hw : |(973588317/2000000000 : ℝ)|=(973588317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1112619977/5000000000 : ℝ)|^4581 ≤ (14437689830519/100000000000000 : ℝ)^3557
        have hw : |(-1112619977/5000000000 : ℝ)|=(1112619977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s0_3 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4137149563/10000000000 : ℝ)*x 0 + (3091903571/10000000000 : ℝ)*x 1 + (2729409263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4137149563/10000000000 : ℝ)^4581 ≤ (8022246633189/25000000000000 : ℝ)^3557 := by
    have hnat : (4137149563 : ℕ)^4581*25000000000000^3557 ≤ 8022246633189^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137149563 10000000000 8022246633189 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091903571/10000000000 : ℝ)^4581 ≤ (5513287496617/25000000000000 : ℝ)^3557 := by
    have hnat : (3091903571 : ℕ)^4581*25000000000000^3557 ≤ 5513287496617^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091903571 10000000000 5513287496617 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729409263/5000000000 : ℝ)^4581 ≤ (22928931731067/50000000000000 : ℝ)^3557 := by
    have hnat : (2729409263 : ℕ)^4581*50000000000000^3557 ≤ 22928931731067^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729409263 5000000000 22928931731067 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4137149563/10000000000 : ℝ), (3091903571/10000000000 : ℝ), (2729409263/5000000000 : ℝ)] ![(8022246633189/25000000000000 : ℝ), (5513287496617/25000000000000 : ℝ), (22928931731067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4137149563/10000000000 : ℝ)|^4581 ≤ (8022246633189/25000000000000 : ℝ)^3557
        have hw : |(4137149563/10000000000 : ℝ)|=(4137149563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091903571/10000000000 : ℝ)|^4581 ≤ (5513287496617/25000000000000 : ℝ)^3557
        have hw : |(3091903571/10000000000 : ℝ)|=(3091903571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729409263/5000000000 : ℝ)|^4581 ≤ (22928931731067/50000000000000 : ℝ)^3557
        have hw : |(2729409263/5000000000 : ℝ)|=(2729409263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s0_4 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-828873213/5000000000 : ℝ)*x 0 + (2446929093/5000000000 : ℝ)*x 1 + (1465815007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (828873213/5000000000 : ℝ)^4581 ≤ (1235209449643/12500000000000 : ℝ)^3557 := by
    have hnat : (828873213 : ℕ)^4581*12500000000000^3557 ≤ 1235209449643^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828873213 5000000000 1235209449643 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2446929093/5000000000 : ℝ)^4581 ≤ (19919447030571/50000000000000 : ℝ)^3557 := by
    have hnat : (2446929093 : ℕ)^4581*50000000000000^3557 ≤ 19919447030571^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2446929093 5000000000 19919447030571 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1465815007/2500000000 : ℝ)^4581 ≤ (50279430319117/100000000000000 : ℝ)^3557 := by
    have hnat : (1465815007 : ℕ)^4581*100000000000000^3557 ≤ 50279430319117^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1465815007 2500000000 50279430319117 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-828873213/5000000000 : ℝ), (2446929093/5000000000 : ℝ), (1465815007/2500000000 : ℝ)] ![(1235209449643/12500000000000 : ℝ), (19919447030571/50000000000000 : ℝ), (50279430319117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-828873213/5000000000 : ℝ)|^4581 ≤ (1235209449643/12500000000000 : ℝ)^3557
        have hw : |(-828873213/5000000000 : ℝ)|=(828873213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2446929093/5000000000 : ℝ)|^4581 ≤ (19919447030571/50000000000000 : ℝ)^3557
        have hw : |(2446929093/5000000000 : ℝ)|=(2446929093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1465815007/2500000000 : ℝ)|^4581 ≤ (50279430319117/100000000000000 : ℝ)^3557
        have hw : |(1465815007/2500000000 : ℝ)|=(1465815007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s0_5 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649013657/1250000000 : ℝ)*x 0 + (-245984309/2000000000 : ℝ)*x 1 + (732907501/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649013657/1250000000 : ℝ)^4581 ≤ (21496420014949/50000000000000 : ℝ)^3557 := by
    have hnat : (649013657 : ℕ)^4581*50000000000000^3557 ≤ 21496420014949^3557*1250000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649013657 1250000000 21496420014949 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245984309/2000000000 : ℝ)^4581 ≤ (3363864925589/50000000000000 : ℝ)^3557 := by
    have hnat : (245984309 : ℕ)^4581*50000000000000^3557 ≤ 3363864925589^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245984309 2000000000 3363864925589 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (732907501/1250000000 : ℝ)^4581 ≤ (50279430098237/100000000000000 : ℝ)^3557 := by
    have hnat : (732907501 : ℕ)^4581*100000000000000^3557 ≤ 50279430098237^3557*1250000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732907501 1250000000 50279430098237 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649013657/1250000000 : ℝ), (-245984309/2000000000 : ℝ), (732907501/1250000000 : ℝ)] ![(21496420014949/50000000000000 : ℝ), (3363864925589/50000000000000 : ℝ), (50279430098237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649013657/1250000000 : ℝ)|^4581 ≤ (21496420014949/50000000000000 : ℝ)^3557
        have hw : |(649013657/1250000000 : ℝ)|=(649013657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-245984309/2000000000 : ℝ)|^4581 ≤ (3363864925589/50000000000000 : ℝ)^3557
        have hw : |(-245984309/2000000000 : ℝ)|=(245984309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(732907501/1250000000 : ℝ)|^4581 ≤ (50279430098237/100000000000000 : ℝ)^3557
        have hw : |(732907501/1250000000 : ℝ)|=(732907501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s0_6 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192108287/10000000000 : ℝ)*x 0 + (586326139/1000000000 : ℝ)*x 1 + (-245984169/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192108287/10000000000 : ℝ)^4581 ≤ (21496414848139/50000000000000 : ℝ)^3557 := by
    have hnat : (5192108287 : ℕ)^4581*50000000000000^3557 ≤ 21496414848139^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192108287 10000000000 21496414848139 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (586326139/1000000000 : ℝ)^4581 ≤ (785616333767/1562500000000 : ℝ)^3557 := by
    have hnat : (586326139 : ℕ)^4581*1562500000000^3557 ≤ 785616333767^3557*1000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586326139 1000000000 785616333767 1562500000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245984169/2000000000 : ℝ)^4581 ≤ (6727724919831/100000000000000 : ℝ)^3557 := by
    have hnat : (245984169 : ℕ)^4581*100000000000000^3557 ≤ 6727724919831^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245984169 2000000000 6727724919831 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192108287/10000000000 : ℝ), (586326139/1000000000 : ℝ), (-245984169/2000000000 : ℝ)] ![(21496414848139/50000000000000 : ℝ), (785616333767/1562500000000 : ℝ), (6727724919831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192108287/10000000000 : ℝ)|^4581 ≤ (21496414848139/50000000000000 : ℝ)^3557
        have hw : |(5192108287/10000000000 : ℝ)|=(5192108287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(586326139/1000000000 : ℝ)|^4581 ≤ (785616333767/1562500000000 : ℝ)^3557
        have hw : |(586326139/1000000000 : ℝ)|=(586326139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-245984169/2000000000 : ℝ)|^4581 ≤ (6727724919831/100000000000000 : ℝ)^3557
        have hw : |(-245984169/2000000000 : ℝ)|=(245984169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s0_7 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4144726661/10000000000 : ℝ)*x 0 + (5398804757/10000000000 : ℝ)*x 1 + (1577027293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4144726661/10000000000 : ℝ)^4581 ≤ (4020586963973/12500000000000 : ℝ)^3557 := by
    have hnat : (4144726661 : ℕ)^4581*12500000000000^3557 ≤ 4020586963973^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144726661 10000000000 4020586963973 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398804757/10000000000 : ℝ)^4581 ≤ (4520959801029/10000000000000 : ℝ)^3557 := by
    have hnat : (5398804757 : ℕ)^4581*10000000000000^3557 ≤ 4520959801029^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398804757 10000000000 4520959801029 10000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577027293/5000000000 : ℝ)^4581 ≤ (5656426568363/25000000000000 : ℝ)^3557 := by
    have hnat : (1577027293 : ℕ)^4581*25000000000000^3557 ≤ 5656426568363^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577027293 5000000000 5656426568363 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4144726661/10000000000 : ℝ), (5398804757/10000000000 : ℝ), (1577027293/5000000000 : ℝ)] ![(4020586963973/12500000000000 : ℝ), (4520959801029/10000000000000 : ℝ), (5656426568363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4144726661/10000000000 : ℝ)|^4581 ≤ (4020586963973/12500000000000 : ℝ)^3557
        have hw : |(4144726661/10000000000 : ℝ)|=(4144726661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398804757/10000000000 : ℝ)|^4581 ≤ (4520959801029/10000000000000 : ℝ)^3557
        have hw : |(5398804757/10000000000 : ℝ)|=(5398804757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577027293/5000000000 : ℝ)|^4581 ≤ (5656426568363/25000000000000 : ℝ)^3557
        have hw : |(1577027293/5000000000 : ℝ)|=(1577027293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1542_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1603/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25101/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4579/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4579 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4579*1^1024 ≤ 0^1024*1^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4579/1024 : ℝ) ≤ (830825372057479407/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4579 ≤ (830825372057479407/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4579*50000000000000000000^1024 ≤ 830825372057479407^1024*5^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 830825372057479407 50000000000000000000 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (830825372057479407/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4579 := by
      have hnat : (1 : ℕ)^1024*1^4579 ≤ 1^4579*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50830825372057479407/50000000000000000000 : ℝ) ≤ (2509230518496183/2500000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (50830825372057479407/50000000000000000000 : ℝ)^1024 ≤ (2509230518496183/2500000000000000 : ℝ)^4579 := by
      have hnat : (50830825372057479407 : ℕ)^1024*2500000000000000^4579 ≤ 2509230518496183^4579*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50830825372057479407 50000000000000000000 2509230518496183 2500000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2509230518496183/2500000000000000 : ℝ)) (X := (50830825372057479407/50000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25830825372057479407/25000000000000000000 : ℝ) ≤ (1259230518496183/1250000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (25830825372057479407/25000000000000000000 : ℝ)^1024 ≤ (1259230518496183/1250000000000000 : ℝ)^4579 := by
      have hnat : (25830825372057479407 : ℕ)^1024*1250000000000000^4579 ≤ 1259230518496183^4579*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25830825372057479407 25000000000000000000 1259230518496183 1250000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1259230518496183/1250000000000000 : ℝ)) (X := (25830825372057479407/25000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9230518496183/1000000000000000 : ℝ)*(0 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9230518496183/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(830825372057479407/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9230518496183/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4579/1024 : ℝ) := by
    rw [show (1 : ℝ)+(9230518496183/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2509230518496183/2500000000000000 : ℝ) by norm_num, show 1+(830825372057479407/50000000000000000000 : ℝ)+(0 : ℝ)=(50830825372057479407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(830825372057479407/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9230518496183/1000000000000000 : ℝ)*(2/5 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9230518496183/1000000000000000 : ℝ)*(2/5 : ℝ)=(1259230518496183/1250000000000000 : ℝ) by norm_num, show 1+2*(830825372057479407/50000000000000000000 : ℝ)=(25830825372057479407/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9230518496183/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9230518496183/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9230518496183/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9230518496183/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9230518496183/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9230518496183/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1654473023/10000000000 : ℝ)*X 0 0+(2945050541/5000000000 : ℝ)*X 0 1+(304246347/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2735741263/5000000000 : ℝ)*X 1 0+(-89009593/400000000 : ℝ)*X 1 1+(2433970809/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5471482457/10000000000 : ℝ)*X 2 0+(973588317/2000000000 : ℝ)*X 2 1+(-1112619977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4137149563/10000000000 : ℝ)*X 0 0+(3091903571/10000000000 : ℝ)*X 0 1+(2729409263/5000000000 : ℝ)*X 0 2+(4137149563/10000000000 : ℝ)*X 1 0+(3091903571/10000000000 : ℝ)*X 1 1+(2729409263/5000000000 : ℝ)*X 1 2+(4137149563/10000000000 : ℝ)*X 2 0+(3091903571/10000000000 : ℝ)*X 2 1+(2729409263/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-828873213/5000000000 : ℝ)*X 0 0+(2446929093/5000000000 : ℝ)*X 0 1+(1465815007/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((649013657/1250000000 : ℝ)*X 1 0+(-245984309/2000000000 : ℝ)*X 1 1+(732907501/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5192108287/10000000000 : ℝ)*X 2 0+(586326139/1000000000 : ℝ)*X 2 1+(-245984169/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4144726661/10000000000 : ℝ)*X 0 0+(5398804757/10000000000 : ℝ)*X 0 1+(1577027293/5000000000 : ℝ)*X 0 2+(4144726661/10000000000 : ℝ)*X 1 0+(5398804757/10000000000 : ℝ)*X 1 1+(1577027293/5000000000 : ℝ)*X 1 2+(4144726661/10000000000 : ℝ)*X 2 0+(5398804757/10000000000 : ℝ)*X 2 1+(1577027293/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18664156689763551790599/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44456537/100000000000000 : ℝ)*(base1) + (142228183/25000000000000 : ℝ)*(base19) + (13914381/2500000000000 : ℝ)*(base23) + (18392479/20000000000000 : ℝ)*(upper3) + (6302401/12500000000000 : ℝ)*(upper5) + (87551088050567/12500000000000 : ℝ)*(major0) + (87551088050567/12500000000000 : ℝ)*(major1) + (87551088050567/12500000000000 : ℝ)*(major2) + (978322943320147/100000000000000 : ℝ)*(sp0) + (489162093435553/50000000000000 : ℝ)*(sp1) + (489162099604299/50000000000000 : ℝ)*(sp2) + (211245810013887/50000000000000 : ℝ)*(sp3) + (1856920227/100000000000000 : ℝ)*(sp4) + (888998749/100000000000000 : ℝ)*(sp7) + (21124627674153/5000000000000 : ℝ)*(f.failure) + (489162377891919/50000000000000 : ℝ)*(f.sum) + (421954314239/6250000000000000000000000000 : ℝ)*base66 + (54724814801739/12500000000000000000000000000 : ℝ)*base68 + (65734793760761/12500000000000000000000000000 : ℝ)*base69 + (31389144601739/12500000000000000000000000000 : ℝ)*base72 + (28655558870489/6250000000000000000000000000 : ℝ)*base74 + (53330893839239/12500000000000000000000000000 : ℝ)*base76 + (58230038726739/12500000000000000000000000000 : ℝ)*base78 + (81271321726739/12500000000000000000000000000 : ℝ)*base80 + (23078840823261/6250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (197989/50000000000000000000 : ℝ)*base89 + (197989/50000000000000000000 : ℝ)*base91 + (197989/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8216720247919114965033/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48431471/25000000000000 : ℝ)*(base19) + (265184223/50000000000000 : ℝ)*(base23) + (512987261/100000000000000 : ℝ)*(base39) + (611221/2500000000000 : ℝ)*(upper2) + (19400593/6250000000000 : ℝ)*(upper5) + (92315260891493/12500000000000 : ℝ)*(major0) + (92315260891493/12500000000000 : ℝ)*(major1) + (738521574144683/100000000000000 : ℝ)*(major2) + (156886963/20000000000000 : ℝ)*(sp1) + (189699957/50000000000000 : ℝ)*(sp2) + (1031560782108251/100000000000000 : ℝ)*(sp4) + (1031559803947551/100000000000000 : ℝ)*(sp5) + (64472524082947/6250000000000 : ℝ)*(sp6) + (445482873690559/100000000000000 : ℝ)*(sp7) + (445482873690559/100000000000000 : ℝ)*(f.failure) + (128945161886939/12500000000000 : ℝ)*(f.sum) + (12392749314741/100000000000000000000000000000 : ℝ)*base65 + (24291440344989/100000000000000000000000000000 : ℝ)*base67 + (10076490146219/12500000000000000000000000000 : ℝ)*base69 + (351712800744989/100000000000000000000000000000 : ℝ)*base71 + (296093542685259/100000000000000000000000000000 : ℝ)*base74 + (95111739521219/12500000000000000000000000000 : ℝ)*base75 + (34091912408719/12500000000000000000000000000 : ℝ)*base77 + (9990128991281/12500000000000000000000000000 : ℝ)*base80 + (7175490941281/6250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (5079267/1000000000000000000000 : ℝ)*base89 + (5079267/1000000000000000000000 : ℝ)*base91 + (5079267/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1542_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1603/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25101/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1542_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1542_s1_0 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-90013027/500000000 : ℝ)*x 0 + (2775672909/5000000000 : ℝ)*x 1 + (1278216087/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90013027/500000000 : ℝ)^4581 ≤ (5494510925879/50000000000000 : ℝ)^3557 := by
    have hnat : (90013027 : ℕ)^4581*50000000000000^3557 ≤ 5494510925879^3557*500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90013027 500000000 5494510925879 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2775672909/5000000000 : ℝ)^4581 ≤ (46861359182879/100000000000000 : ℝ)^3557 := by
    have hnat : (2775672909 : ℕ)^4581*100000000000000^3557 ≤ 46861359182879^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2775672909 5000000000 46861359182879 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1278216087/2500000000 : ℝ)^4581 ≤ (42149618942883/100000000000000 : ℝ)^3557 := by
    have hnat : (1278216087 : ℕ)^4581*100000000000000^3557 ≤ 42149618942883^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278216087 2500000000 42149618942883 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-90013027/500000000 : ℝ), (2775672909/5000000000 : ℝ), (1278216087/2500000000 : ℝ)] ![(5494510925879/50000000000000 : ℝ), (46861359182879/100000000000000 : ℝ), (42149618942883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-90013027/500000000 : ℝ)|^4581 ≤ (5494510925879/50000000000000 : ℝ)^3557
        have hw : |(-90013027/500000000 : ℝ)|=(90013027/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2775672909/5000000000 : ℝ)|^4581 ≤ (46861359182879/100000000000000 : ℝ)^3557
        have hw : |(2775672909/5000000000 : ℝ)|=(2775672909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1278216087/2500000000 : ℝ)|^4581 ≤ (42149618942883/100000000000000 : ℝ)^3557
        have hw : |(1278216087/2500000000 : ℝ)|=(1278216087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s1_1 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690628231/5000000000 : ℝ)*x 0 + (-203032229/1000000000 : ℝ)*x 1 + (2556432481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690628231/5000000000 : ℝ)^4581 ≤ (9004086585081/20000000000000 : ℝ)^3557 := by
    have hnat : (2690628231 : ℕ)^4581*20000000000000^3557 ≤ 9004086585081^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690628231 5000000000 9004086585081 20000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203032229/1000000000 : ℝ)^4581 ≤ (6414970800247/50000000000000 : ℝ)^3557 := by
    have hnat : (203032229 : ℕ)^4581*50000000000000^3557 ≤ 6414970800247^3557*1000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203032229 1000000000 6414970800247 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2556432481/5000000000 : ℝ)^4581 ≤ (42149625461781/100000000000000 : ℝ)^3557 := by
    have hnat : (2556432481 : ℕ)^4581*100000000000000^3557 ≤ 42149625461781^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2556432481 5000000000 42149625461781 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690628231/5000000000 : ℝ), (-203032229/1000000000 : ℝ), (2556432481/5000000000 : ℝ)] ![(9004086585081/20000000000000 : ℝ), (6414970800247/50000000000000 : ℝ), (42149625461781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690628231/5000000000 : ℝ)|^4581 ≤ (9004086585081/20000000000000 : ℝ)^3557
        have hw : |(2690628231/5000000000 : ℝ)|=(2690628231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-203032229/1000000000 : ℝ)|^4581 ≤ (6414970800247/50000000000000 : ℝ)^3557
        have hw : |(-203032229/1000000000 : ℝ)|=(203032229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2556432481/5000000000 : ℝ)|^4581 ≤ (42149625461781/100000000000000 : ℝ)^3557
        have hw : |(2556432481/5000000000 : ℝ)|=(2556432481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s1_2 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690628551/5000000000 : ℝ)*x 0 + (1278216113/2500000000 : ℝ)*x 1 + (-2030322107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690628551/5000000000 : ℝ)^4581 ≤ (45020439821169/100000000000000 : ℝ)^3557 := by
    have hnat : (2690628551 : ℕ)^4581*100000000000000^3557 ≤ 45020439821169^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690628551 5000000000 45020439821169 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1278216113/2500000000 : ℝ)^4581 ≤ (42149620047061/100000000000000 : ℝ)^3557 := by
    have hnat : (1278216113 : ℕ)^4581*100000000000000^3557 ≤ 42149620047061^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278216113 2500000000 42149620047061 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2030322107/10000000000 : ℝ)^4581 ≤ (1603742513897/12500000000000 : ℝ)^3557 := by
    have hnat : (2030322107 : ℕ)^4581*12500000000000^3557 ≤ 1603742513897^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030322107 10000000000 1603742513897 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690628551/5000000000 : ℝ), (1278216113/2500000000 : ℝ), (-2030322107/10000000000 : ℝ)] ![(45020439821169/100000000000000 : ℝ), (42149620047061/100000000000000 : ℝ), (1603742513897/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690628551/5000000000 : ℝ)|^4581 ≤ (45020439821169/100000000000000 : ℝ)^3557
        have hw : |(2690628551/5000000000 : ℝ)|=(2690628551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1278216113/2500000000 : ℝ)|^4581 ≤ (42149620047061/100000000000000 : ℝ)^3557
        have hw : |(1278216113/2500000000 : ℝ)|=(1278216113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2030322107/10000000000 : ℝ)|^4581 ≤ (1603742513897/12500000000000 : ℝ)^3557
        have hw : |(-2030322107/10000000000 : ℝ)|=(2030322107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s1_3 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2119332893/5000000000 : ℝ)*x 0 + (469506229/1250000000 : ℝ)*x 1 + (37276547/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119332893/5000000000 : ℝ)^4581 ≤ (3310661458559/10000000000000 : ℝ)^3557 := by
    have hnat : (2119332893 : ℕ)^4581*10000000000000^3557 ≤ 3310661458559^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119332893 5000000000 3310661458559 10000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469506229/1250000000 : ℝ)^4581 ≤ (28333727267863/100000000000000 : ℝ)^3557 := by
    have hnat : (469506229 : ℕ)^4581*100000000000000^3557 ≤ 28333727267863^3557*1250000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469506229 1250000000 28333727267863 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37276547/78125000 : ℝ)^4581 ≤ (7711931625691/20000000000000 : ℝ)^3557 := by
    have hnat : (37276547 : ℕ)^4581*20000000000000^3557 ≤ 7711931625691^3557*78125000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37276547 78125000 7711931625691 20000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2119332893/5000000000 : ℝ), (469506229/1250000000 : ℝ), (37276547/78125000 : ℝ)] ![(3310661458559/10000000000000 : ℝ), (28333727267863/100000000000000 : ℝ), (7711931625691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2119332893/5000000000 : ℝ)|^4581 ≤ (3310661458559/10000000000000 : ℝ)^3557
        have hw : |(2119332893/5000000000 : ℝ)|=(2119332893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(469506229/1250000000 : ℝ)|^4581 ≤ (28333727267863/100000000000000 : ℝ)^3557
        have hw : |(469506229/1250000000 : ℝ)|=(469506229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(37276547/78125000 : ℝ)|^4581 ≤ (7711931625691/20000000000000 : ℝ)^3557
        have hw : |(37276547/78125000 : ℝ)|=(37276547/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s1_4 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-180051089/1000000000 : ℝ)*x 0 + (5117565877/10000000000 : ℝ)*x 1 + (5546572113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (180051089/1000000000 : ℝ)^4581 ≤ (10990989993579/100000000000000 : ℝ)^3557 := by
    have hnat : (180051089 : ℕ)^4581*100000000000000^3557 ≤ 10990989993579^3557*1000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180051089 1000000000 10990989993579 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5117565877/10000000000 : ℝ)^4581 ≤ (42199542140633/100000000000000 : ℝ)^3557 := by
    have hnat : (5117565877 : ℕ)^4581*100000000000000^3557 ≤ 42199542140633^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5117565877 10000000000 42199542140633 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5546572113/10000000000 : ℝ)^4581 ≤ (4680946784927/10000000000000 : ℝ)^3557 := by
    have hnat : (5546572113 : ℕ)^4581*10000000000000^3557 ≤ 4680946784927^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5546572113 10000000000 4680946784927 10000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-180051089/1000000000 : ℝ), (5117565877/10000000000 : ℝ), (5546572113/10000000000 : ℝ)] ![(10990989993579/100000000000000 : ℝ), (42199542140633/100000000000000 : ℝ), (4680946784927/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-180051089/1000000000 : ℝ)|^4581 ≤ (10990989993579/100000000000000 : ℝ)^3557
        have hw : |(-180051089/1000000000 : ℝ)|=(180051089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5117565877/10000000000 : ℝ)|^4581 ≤ (42199542140633/100000000000000 : ℝ)^3557
        have hw : |(5117565877/10000000000 : ℝ)|=(5117565877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5546572113/10000000000 : ℝ)|^4581 ≤ (4680946784927/10000000000000 : ℝ)^3557
        have hw : |(5546572113/10000000000 : ℝ)|=(5546572113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s1_5 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632682893/5000000000 : ℝ)*x 0 + (-319323119/2000000000 : ℝ)*x 1 + (5546571881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632682893/5000000000 : ℝ)^4581 ≤ (43775644444297/100000000000000 : ℝ)^3557 := by
    have hnat : (2632682893 : ℕ)^4581*100000000000000^3557 ≤ 43775644444297^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632682893 5000000000 43775644444297 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (319323119/2000000000 : ℝ)^4581 ≤ (941489021833/10000000000000 : ℝ)^3557 := by
    have hnat : (319323119 : ℕ)^4581*10000000000000^3557 ≤ 941489021833^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319323119 2000000000 941489021833 10000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5546571881/10000000000 : ℝ)^4581 ≤ (23404732663843/50000000000000 : ℝ)^3557 := by
    have hnat : (5546571881 : ℕ)^4581*50000000000000^3557 ≤ 23404732663843^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5546571881 10000000000 23404732663843 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632682893/5000000000 : ℝ), (-319323119/2000000000 : ℝ), (5546571881/10000000000 : ℝ)] ![(43775644444297/100000000000000 : ℝ), (941489021833/10000000000000 : ℝ), (23404732663843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632682893/5000000000 : ℝ)|^4581 ≤ (43775644444297/100000000000000 : ℝ)^3557
        have hw : |(2632682893/5000000000 : ℝ)|=(2632682893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-319323119/2000000000 : ℝ)|^4581 ≤ (941489021833/10000000000000 : ℝ)^3557
        have hw : |(-319323119/2000000000 : ℝ)|=(319323119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5546571881/10000000000 : ℝ)|^4581 ≤ (23404732663843/50000000000000 : ℝ)^3557
        have hw : |(5546571881/10000000000 : ℝ)|=(5546571881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s1_6 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265366517/10000000000 : ℝ)*x 0 + (554657173/1000000000 : ℝ)*x 1 + (-79830739/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265366517/10000000000 : ℝ)^4581 ≤ (21887826135671/50000000000000 : ℝ)^3557 := by
    have hnat : (5265366517 : ℕ)^4581*50000000000000^3557 ≤ 21887826135671^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265366517 10000000000 21887826135671 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554657173/1000000000 : ℝ)^4581 ≤ (46809463686483/100000000000000 : ℝ)^3557 := by
    have hnat : (554657173 : ℕ)^4581*100000000000000^3557 ≤ 46809463686483^3557*1000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554657173 1000000000 46809463686483 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79830739/500000000 : ℝ)^4581 ≤ (376595361157/4000000000000 : ℝ)^3557 := by
    have hnat : (79830739 : ℕ)^4581*4000000000000^3557 ≤ 376595361157^3557*500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79830739 500000000 376595361157 4000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265366517/10000000000 : ℝ), (554657173/1000000000 : ℝ), (-79830739/500000000 : ℝ)] ![(21887826135671/50000000000000 : ℝ), (46809463686483/100000000000000 : ℝ), (376595361157/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265366517/10000000000 : ℝ)|^4581 ≤ (21887826135671/50000000000000 : ℝ)^3557
        have hw : |(5265366517/10000000000 : ℝ)|=(5265366517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(554657173/1000000000 : ℝ)|^4581 ≤ (46809463686483/100000000000000 : ℝ)^3557
        have hw : |(554657173/1000000000 : ℝ)|=(554657173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-79830739/500000000 : ℝ)|^4581 ≤ (376595361157/4000000000000 : ℝ)^3557
        have hw : |(-79830739/500000000 : ℝ)|=(79830739/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s1_7 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (847849259/2000000000 : ℝ)*x 0 + (1190127729/2500000000 : ℝ)*x 1 + (1883551851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847849259/2000000000 : ℝ)^4581 ≤ (8278113534443/25000000000000 : ℝ)^3557 := by
    have hnat : (847849259 : ℕ)^4581*25000000000000^3557 ≤ 8278113534443^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847849259 2000000000 8278113534443 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1190127729/2500000000 : ℝ)^4581 ≤ (38446383296027/100000000000000 : ℝ)^3557 := by
    have hnat : (1190127729 : ℕ)^4581*100000000000000^3557 ≤ 38446383296027^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1190127729 2500000000 38446383296027 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1883551851/5000000000 : ℝ)^4581 ≤ (28441162554901/100000000000000 : ℝ)^3557 := by
    have hnat : (1883551851 : ℕ)^4581*100000000000000^3557 ≤ 28441162554901^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883551851 5000000000 28441162554901 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(847849259/2000000000 : ℝ), (1190127729/2500000000 : ℝ), (1883551851/5000000000 : ℝ)] ![(8278113534443/25000000000000 : ℝ), (38446383296027/100000000000000 : ℝ), (28441162554901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(847849259/2000000000 : ℝ)|^4581 ≤ (8278113534443/25000000000000 : ℝ)^3557
        have hw : |(847849259/2000000000 : ℝ)|=(847849259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1190127729/2500000000 : ℝ)|^4581 ≤ (38446383296027/100000000000000 : ℝ)^3557
        have hw : |(1190127729/2500000000 : ℝ)|=(1190127729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1883551851/5000000000 : ℝ)|^4581 ≤ (28441162554901/100000000000000 : ℝ)^3557
        have hw : |(1883551851/5000000000 : ℝ)|=(1883551851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1542_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8741/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18021/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1603/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1603/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1603/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1603/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1603/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1603/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1603/50000 : ℝ) ^ (4579/1024 : ℝ) ≤ (4170397070051/20000000000000000000 : ℝ) := by
    have hpowers : (1603/50000 : ℝ)^4579 ≤ (4170397070051/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1603 : ℕ)^4579*20000000000000000000^1024 ≤ 4170397070051^1024*50000^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1603 50000 4170397070051 20000000000000000000 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1603/50000 : ℝ)) (X := (4170397070051/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25101/100000 : ℝ) ^ (4579/1024 : ℝ) ≤ (41365715447858241/20000000000000000000 : ℝ) := by
    have hpowers : (25101/100000 : ℝ)^4579 ≤ (41365715447858241/20000000000000000000 : ℝ)^1024 := by
      have hnat : (25101 : ℕ)^4579*20000000000000000000^1024 ≤ 41365715447858241^1024*100000^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25101 100000 41365715447858241 20000000000000000000 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25101/100000 : ℝ)) (X := (41365715447858241/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000004170397070051/10000000000000000000 : ℝ) ≤ (5000000466312067/5000000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (10000004170397070051/10000000000000000000 : ℝ)^1024 ≤ (5000000466312067/5000000000000000 : ℝ)^4579 := by
      have hnat : (10000004170397070051 : ℕ)^1024*5000000000000000^4579 ≤ 5000000466312067^4579*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000004170397070051 10000000000000000000 5000000466312067 5000000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000466312067/5000000000000000 : ℝ)) (X := (10000004170397070051/10000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5010342471461232073/5000000000000000000 : ℝ) ≤ (10004622056033201/10000000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (5010342471461232073/5000000000000000000 : ℝ)^1024 ≤ (10004622056033201/10000000000000000 : ℝ)^4579 := by
      have hnat : (5010342471461232073 : ℕ)^1024*10000000000000000^4579 ≤ 10004622056033201^4579*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5010342471461232073 5000000000000000000 10004622056033201 10000000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004622056033201/10000000000000000 : ℝ)) (X := (5010342471461232073/5000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10041365715447858241/10000000000000000000 : ℝ) ≤ (2502310794860567/2500000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (10041365715447858241/10000000000000000000 : ℝ)^1024 ≤ (2502310794860567/2500000000000000 : ℝ)^4579 := by
      have hnat : (10041365715447858241 : ℕ)^1024*2500000000000000^4579 ≤ 2502310794860567^4579*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10041365715447858241 10000000000000000000 2502310794860567 2500000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502310794860567/2500000000000000 : ℝ)) (X := (10041365715447858241/10000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4170397070051/20000000000000000000 : ℝ) ≤ ((109460194888253238163/109475000000000000000 : ℝ)+2*(4621123409067/2189500000000000 : ℝ)*(1603/50000 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (109460194888253238163/109475000000000000000 : ℝ)+2*(4621123409067/2189500000000000 : ℝ)*(1603/50000 : ℝ)=(5000000466312067/5000000000000000 : ℝ) by norm_num, show 1+2*(4170397070051/20000000000000000000 : ℝ)=(10000004170397070051/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(41365715447858241/20000000000000000000 : ℝ)+(4170397070051/20000000000000000000 : ℝ) ≤ ((109460194888253238163/109475000000000000000 : ℝ)+(4621123409067/2189500000000000 : ℝ)*((25101/100000 : ℝ)+(1603/50000 : ℝ)))^(4579/1024 : ℝ) := by
    rw [show (109460194888253238163/109475000000000000000 : ℝ)+(4621123409067/2189500000000000 : ℝ)*((25101/100000 : ℝ)+(1603/50000 : ℝ))=(10004622056033201/10000000000000000 : ℝ) by norm_num, show 1+(41365715447858241/20000000000000000000 : ℝ)+(4170397070051/20000000000000000000 : ℝ)=(5010342471461232073/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(41365715447858241/20000000000000000000 : ℝ) ≤ ((109460194888253238163/109475000000000000000 : ℝ)+2*(4621123409067/2189500000000000 : ℝ)*(25101/100000 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (109460194888253238163/109475000000000000000 : ℝ)+2*(4621123409067/2189500000000000 : ℝ)*(25101/100000 : ℝ)=(2502310794860567/2500000000000000 : ℝ) by norm_num, show 1+2*(41365715447858241/20000000000000000000 : ℝ)=(10041365715447858241/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (109460194888253238163/109475000000000000000 : ℝ)*(X 1 0+X 2 0)+(4621123409067/2189500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (1603/50000 : ℝ)) (hi := (25101/100000 : ℝ)) (c := (109460194888253238163/109475000000000000000 : ℝ)) (alpha := (4621123409067/2189500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (109460194888253238163/109475000000000000000 : ℝ)*(X 0 1+X 2 1)+(4621123409067/2189500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (1603/50000 : ℝ)) (hi := (25101/100000 : ℝ)) (c := (109460194888253238163/109475000000000000000 : ℝ)) (alpha := (4621123409067/2189500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (109460194888253238163/109475000000000000000 : ℝ)*(X 0 2+X 1 2)+(4621123409067/2189500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (1603/50000 : ℝ)) (hi := (25101/100000 : ℝ)) (c := (109460194888253238163/109475000000000000000 : ℝ)) (alpha := (4621123409067/2189500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-90013027/500000000 : ℝ)*X 0 0+(2775672909/5000000000 : ℝ)*X 0 1+(1278216087/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2690628231/5000000000 : ℝ)*X 1 0+(-203032229/1000000000 : ℝ)*X 1 1+(2556432481/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2690628551/5000000000 : ℝ)*X 2 0+(1278216113/2500000000 : ℝ)*X 2 1+(-2030322107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2119332893/5000000000 : ℝ)*X 0 0+(469506229/1250000000 : ℝ)*X 0 1+(37276547/78125000 : ℝ)*X 0 2+(2119332893/5000000000 : ℝ)*X 1 0+(469506229/1250000000 : ℝ)*X 1 1+(37276547/78125000 : ℝ)*X 1 2+(2119332893/5000000000 : ℝ)*X 2 0+(469506229/1250000000 : ℝ)*X 2 1+(37276547/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-180051089/1000000000 : ℝ)*X 0 0+(5117565877/10000000000 : ℝ)*X 0 1+(5546572113/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2632682893/5000000000 : ℝ)*X 1 0+(-319323119/2000000000 : ℝ)*X 1 1+(5546571881/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5265366517/10000000000 : ℝ)*X 2 0+(554657173/1000000000 : ℝ)*X 2 1+(-79830739/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((847849259/2000000000 : ℝ)*X 0 0+(1190127729/2500000000 : ℝ)*X 0 1+(1883551851/5000000000 : ℝ)*X 0 2+(847849259/2000000000 : ℝ)*X 1 0+(1190127729/2500000000 : ℝ)*X 1 1+(1883551851/5000000000 : ℝ)*X 1 2+(847849259/2000000000 : ℝ)*X 2 0+(1190127729/2500000000 : ℝ)*X 2 1+(1883551851/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8599791594512174044487929527/1368437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (488775443/50000000000000 : ℝ)*(base19) + (235379309/20000000000000 : ℝ)*(base23) + (4287321/4000000000000 : ℝ)*(upper3) + (38686511/100000000000000 : ℝ)*(upper4) + (204689021/100000000000000 : ℝ)*(upper5) + (408188890601319/25000000000000 : ℝ)*(major0) + (408188890601319/25000000000000 : ℝ)*(major1) + (408188890601319/25000000000000 : ℝ)*(major2) + (28507586837067/1250000000000 : ℝ)*(sp0) + (45612354841433/2000000000000 : ℝ)*(sp1) + (285077192840749/12500000000000 : ℝ)*(sp2) + (492444019607823/50000000000000 : ℝ)*(sp3) + (1471582147/12500000000000 : ℝ)*(sp4) + (166259711/4000000000000 : ℝ)*(sp7) + (492446097854211/50000000000000 : ℝ)*(f.failure) + (285077339952817/12500000000000 : ℝ)*(f.sum) + (630434221331517/109475000000000000000000000000 : ℝ)*base65 + (37189097232010086997/2736875000000000000000000000000000 : ℝ)*base67 + (17461214110353836997/2736875000000000000000000000000000 : ℝ)*base69 + (38024507862145711997/2736875000000000000000000000000000 : ℝ)*base71 + (134316119793823/27368750000000000000000000000 : ℝ)*base73 + (22024654492211336997/2736875000000000000000000000000000 : ℝ)*base75 + (18700821400248211997/2736875000000000000000000000000000 : ℝ)*base77 + (6728804563755086997/2736875000000000000000000000000000 : ℝ)*base79 + (131920879347271/54737500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2062743/500000000000000000000 : ℝ)*base89 + (2062743/500000000000000000000 : ℝ)*base91 + (2062743/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79758276339003858812313/21895000000000000000000000000 : ℝ) := by norm_num
    linear_combination (330086869/100000000000000 : ℝ)*(base19) + (800137937/100000000000000 : ℝ)*(base23) + (41220329/50000000000000 : ℝ)*(upper3) + (24150819/100000000000000 : ℝ)*(lower4) + (69280431/50000000000000 : ℝ)*(upper5) + (166880354246541/10000000000000 : ℝ)*(major0) + (166880354246541/10000000000000 : ℝ)*(major1) + (166880354246541/10000000000000 : ℝ)*(major2) + (241698813/100000000000000 : ℝ)*(sp1) + (2405521317/50000000000000 : ℝ)*(sp2) + (36421411191239/1562500000000 : ℝ)*(sp4) + (1165484872226807/50000000000000 : ℝ)*(sp5) + (582741176264681/25000000000000 : ℝ)*(sp6) + (1006636647266117/100000000000000 : ℝ)*(sp7) + (1006636647266117/100000000000000 : ℝ)*(f.failure) + (36421411191239/1562500000000 : ℝ)*(f.sum) + (33571420002631/21895000000000000000000000000 : ℝ)*base66 + (2559074003015294183/1094750000000000000000000000000000 : ℝ)*base67 + (2430448167240205817/1094750000000000000000000000000000 : ℝ)*base70 + (1862819354039455817/1094750000000000000000000000000000 : ℝ)*base72 + (15059166251527/10947500000000000000000000000 : ℝ)*base73 + (5974773099082205817/1094750000000000000000000000000000 : ℝ)*base76 + (2108932807382044183/1094750000000000000000000000000000 : ℝ)*base77 + (6076268744019294183/1094750000000000000000000000000000 : ℝ)*base79 + (550077716487/10947500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2085521/1000000000000000000000 : ℝ)*base89 + (2085521/1000000000000000000000 : ℝ)*base91 + (2085521/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1542_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8741/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18021/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1542_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1542_s2_0 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1821534617/10000000000 : ℝ)*x 0 + (1362226163/2500000000 : ℝ)*x 1 + (5201481927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1821534617/10000000000 : ℝ)^4581 ≤ (5578274823371/50000000000000 : ℝ)^3557 := by
    have hnat : (1821534617 : ℕ)^4581*50000000000000^3557 ≤ 5578274823371^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821534617 10000000000 5578274823371 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362226163/2500000000 : ℝ)^4581 ≤ (142970725649/312500000000 : ℝ)^3557 := by
    have hnat : (1362226163 : ℕ)^4581*312500000000^3557 ≤ 142970725649^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362226163 2500000000 142970725649 312500000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5201481927/10000000000 : ℝ)^4581 ≤ (43092818133661/100000000000000 : ℝ)^3557 := by
    have hnat : (5201481927 : ℕ)^4581*100000000000000^3557 ≤ 43092818133661^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201481927 10000000000 43092818133661 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1821534617/10000000000 : ℝ), (1362226163/2500000000 : ℝ), (5201481927/10000000000 : ℝ)] ![(5578274823371/50000000000000 : ℝ), (142970725649/312500000000 : ℝ), (43092818133661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1821534617/10000000000 : ℝ)|^4581 ≤ (5578274823371/50000000000000 : ℝ)^3557
        have hw : |(-1821534617/10000000000 : ℝ)|=(1821534617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1362226163/2500000000 : ℝ)|^4581 ≤ (142970725649/312500000000 : ℝ)^3557
        have hw : |(1362226163/2500000000 : ℝ)|=(1362226163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5201481927/10000000000 : ℝ)|^4581 ≤ (43092818133661/100000000000000 : ℝ)^3557
        have hw : |(5201481927/10000000000 : ℝ)|=(5201481927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s2_1 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354995553/10000000000 : ℝ)*x 0 + (-1948693207/10000000000 : ℝ)*x 1 + (1300370569/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354995553/10000000000 : ℝ)^4581 ≤ (44737680311441/100000000000000 : ℝ)^3557 := by
    have hnat : (5354995553 : ℕ)^4581*100000000000000^3557 ≤ 44737680311441^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354995553 10000000000 44737680311441 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1948693207/10000000000 : ℝ)^4581 ≤ (12169497819691/100000000000000 : ℝ)^3557 := by
    have hnat : (1948693207 : ℕ)^4581*100000000000000^3557 ≤ 12169497819691^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948693207 10000000000 12169497819691 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1300370569/2500000000 : ℝ)^4581 ≤ (10773205464351/25000000000000 : ℝ)^3557 := by
    have hnat : (1300370569 : ℕ)^4581*25000000000000^3557 ≤ 10773205464351^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300370569 2500000000 10773205464351 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354995553/10000000000 : ℝ), (-1948693207/10000000000 : ℝ), (1300370569/2500000000 : ℝ)] ![(44737680311441/100000000000000 : ℝ), (12169497819691/100000000000000 : ℝ), (10773205464351/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354995553/10000000000 : ℝ)|^4581 ≤ (44737680311441/100000000000000 : ℝ)^3557
        have hw : |(5354995553/10000000000 : ℝ)|=(5354995553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1948693207/10000000000 : ℝ)|^4581 ≤ (12169497819691/100000000000000 : ℝ)^3557
        have hw : |(-1948693207/10000000000 : ℝ)|=(1948693207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1300370569/2500000000 : ℝ)|^4581 ≤ (10773205464351/25000000000000 : ℝ)^3557
        have hw : |(1300370569/2500000000 : ℝ)|=(1300370569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s2_2 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677498127/5000000000 : ℝ)*x 0 + (2600740907/5000000000 : ℝ)*x 1 + (-1948692881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677498127/5000000000 : ℝ)^4581 ≤ (44737687853827/100000000000000 : ℝ)^3557 := by
    have hnat : (2677498127 : ℕ)^4581*100000000000000^3557 ≤ 44737687853827^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677498127 5000000000 44737687853827 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2600740907/5000000000 : ℝ)^4581 ≤ (43092816927979/100000000000000 : ℝ)^3557 := by
    have hnat : (2600740907 : ℕ)^4581*100000000000000^3557 ≤ 43092816927979^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600740907 5000000000 43092816927979 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1948692881/10000000000 : ℝ)^4581 ≤ (3042373799437/25000000000000 : ℝ)^3557 := by
    have hnat : (1948692881 : ℕ)^4581*25000000000000^3557 ≤ 3042373799437^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948692881 10000000000 3042373799437 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677498127/5000000000 : ℝ), (2600740907/5000000000 : ℝ), (-1948692881/10000000000 : ℝ)] ![(44737687853827/100000000000000 : ℝ), (43092816927979/100000000000000 : ℝ), (3042373799437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677498127/5000000000 : ℝ)|^4581 ≤ (44737687853827/100000000000000 : ℝ)^3557
        have hw : |(2677498127/5000000000 : ℝ)|=(2677498127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2600740907/5000000000 : ℝ)|^4581 ≤ (43092816927979/100000000000000 : ℝ)^3557
        have hw : |(2600740907/5000000000 : ℝ)|=(2600740907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1948692881/10000000000 : ℝ)|^4581 ≤ (3042373799437/25000000000000 : ℝ)^3557
        have hw : |(-1948692881/10000000000 : ℝ)|=(1948692881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s2_3 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4254015441/10000000000 : ℝ)*x 0 + (993883039/2500000000 : ℝ)*x 1 + (4548465991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4254015441/10000000000 : ℝ)^4581 ≤ (519704683551/1562500000000 : ℝ)^3557 := by
    have hnat : (4254015441 : ℕ)^4581*1562500000000^3557 ≤ 519704683551^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254015441 10000000000 519704683551 1562500000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993883039/2500000000 : ℝ)^4581 ≤ (15241859872263/50000000000000 : ℝ)^3557 := by
    have hnat : (993883039 : ℕ)^4581*50000000000000^3557 ≤ 15241859872263^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993883039 2500000000 15241859872263 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4548465991/10000000000 : ℝ)^4581 ≤ (36255180487681/100000000000000 : ℝ)^3557 := by
    have hnat : (4548465991 : ℕ)^4581*100000000000000^3557 ≤ 36255180487681^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4548465991 10000000000 36255180487681 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4254015441/10000000000 : ℝ), (993883039/2500000000 : ℝ), (4548465991/10000000000 : ℝ)] ![(519704683551/1562500000000 : ℝ), (15241859872263/50000000000000 : ℝ), (36255180487681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4254015441/10000000000 : ℝ)|^4581 ≤ (519704683551/1562500000000 : ℝ)^3557
        have hw : |(4254015441/10000000000 : ℝ)|=(4254015441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(993883039/2500000000 : ℝ)|^4581 ≤ (15241859872263/50000000000000 : ℝ)^3557
        have hw : |(993883039/2500000000 : ℝ)|=(993883039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4548465991/10000000000 : ℝ)|^4581 ≤ (36255180487681/100000000000000 : ℝ)^3557
        have hw : |(4548465991/10000000000 : ℝ)|=(4548465991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s2_4 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-364315827/2000000000 : ℝ)*x 0 + (2601493653/5000000000 : ℝ)*x 1 + (5447386681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (364315827/2000000000 : ℝ)^4581 ≤ (11156900807577/100000000000000 : ℝ)^3557 := by
    have hnat : (364315827 : ℕ)^4581*100000000000000^3557 ≤ 11156900807577^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364315827 2000000000 11156900807577 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2601493653/5000000000 : ℝ)^4581 ≤ (43108880819787/100000000000000 : ℝ)^3557 := by
    have hnat : (2601493653 : ℕ)^4581*100000000000000^3557 ≤ 43108880819787^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601493653 5000000000 43108880819787 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5447386681/10000000000 : ℝ)^4581 ≤ (22867109180431/50000000000000 : ℝ)^3557 := by
    have hnat : (5447386681 : ℕ)^4581*50000000000000^3557 ≤ 22867109180431^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447386681 10000000000 22867109180431 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-364315827/2000000000 : ℝ), (2601493653/5000000000 : ℝ), (5447386681/10000000000 : ℝ)] ![(11156900807577/100000000000000 : ℝ), (43108880819787/100000000000000 : ℝ), (22867109180431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-364315827/2000000000 : ℝ)|^4581 ≤ (11156900807577/100000000000000 : ℝ)^3557
        have hw : |(-364315827/2000000000 : ℝ)|=(364315827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2601493653/5000000000 : ℝ)|^4581 ≤ (43108880819787/100000000000000 : ℝ)^3557
        have hw : |(2601493653/5000000000 : ℝ)|=(2601493653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5447386681/10000000000 : ℝ)|^4581 ≤ (22867109180431/50000000000000 : ℝ)^3557
        have hw : |(5447386681/10000000000 : ℝ)|=(5447386681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s2_5 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644878109/5000000000 : ℝ)*x 0 + (-851394313/5000000000 : ℝ)*x 1 + (272369339/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644878109/5000000000 : ℝ)^4581 ≤ (44036974331769/100000000000000 : ℝ)^3557 := by
    have hnat : (2644878109 : ℕ)^4581*100000000000000^3557 ≤ 44036974331769^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644878109 5000000000 44036974331769 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (851394313/5000000000 : ℝ)^4581 ≤ (2557201557137/25000000000000 : ℝ)^3557 := by
    have hnat : (851394313 : ℕ)^4581*25000000000000^3557 ≤ 2557201557137^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851394313 5000000000 2557201557137 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272369339/500000000 : ℝ)^4581 ≤ (11433554857827/25000000000000 : ℝ)^3557 := by
    have hnat : (272369339 : ℕ)^4581*25000000000000^3557 ≤ 11433554857827^3557*500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272369339 500000000 11433554857827 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644878109/5000000000 : ℝ), (-851394313/5000000000 : ℝ), (272369339/500000000 : ℝ)] ![(44036974331769/100000000000000 : ℝ), (2557201557137/25000000000000 : ℝ), (11433554857827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644878109/5000000000 : ℝ)|^4581 ≤ (44036974331769/100000000000000 : ℝ)^3557
        have hw : |(2644878109/5000000000 : ℝ)|=(2644878109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-851394313/5000000000 : ℝ)|^4581 ≤ (2557201557137/25000000000000 : ℝ)^3557
        have hw : |(-851394313/5000000000 : ℝ)|=(851394313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272369339/500000000 : ℝ)|^4581 ≤ (11433554857827/25000000000000 : ℝ)^3557
        have hw : |(272369339/500000000 : ℝ)|=(272369339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s2_6 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289756239/10000000000 : ℝ)*x 0 + (340461691/625000000 : ℝ)*x 1 + (-170278821/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289756239/10000000000 : ℝ)^4581 ≤ (22018487278461/50000000000000 : ℝ)^3557 := by
    have hnat : (5289756239 : ℕ)^4581*50000000000000^3557 ≤ 22018487278461^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289756239 10000000000 22018487278461 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340461691/625000000 : ℝ)^4581 ≤ (45734222415581/100000000000000 : ℝ)^3557 := by
    have hnat : (340461691 : ℕ)^4581*100000000000000^3557 ≤ 45734222415581^3557*625000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340461691 625000000 45734222415581 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170278821/1000000000 : ℝ)^4581 ≤ (10228803010193/100000000000000 : ℝ)^3557 := by
    have hnat : (170278821 : ℕ)^4581*100000000000000^3557 ≤ 10228803010193^3557*1000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170278821 1000000000 10228803010193 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289756239/10000000000 : ℝ), (340461691/625000000 : ℝ), (-170278821/1000000000 : ℝ)] ![(22018487278461/50000000000000 : ℝ), (45734222415581/100000000000000 : ℝ), (10228803010193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289756239/10000000000 : ℝ)|^4581 ≤ (22018487278461/50000000000000 : ℝ)^3557
        have hw : |(5289756239/10000000000 : ℝ)|=(5289756239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340461691/625000000 : ℝ)|^4581 ≤ (45734222415581/100000000000000 : ℝ)^3557
        have hw : |(340461691/625000000 : ℝ)|=(340461691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-170278821/1000000000 : ℝ)|^4581 ≤ (10228803010193/100000000000000 : ℝ)^3557
        have hw : |(-170278821/1000000000 : ℝ)|=(170278821/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s2_7 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (850824009/2000000000 : ℝ)*x 0 + (4544980159/10000000000 : ℝ)*x 1 + (795809647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (850824009/2000000000 : ℝ)^4581 ≤ (8315538268919/25000000000000 : ℝ)^3557 := by
    have hnat : (850824009 : ℕ)^4581*25000000000000^3557 ≤ 8315538268919^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850824009 2000000000 8315538268919 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4544980159/10000000000 : ℝ)^4581 ≤ (36219400508883/100000000000000 : ℝ)^3557 := by
    have hnat : (4544980159 : ℕ)^4581*100000000000000^3557 ≤ 36219400508883^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544980159 10000000000 36219400508883 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (795809647/2000000000 : ℝ)^4581 ≤ (1907402900277/6250000000000 : ℝ)^3557 := by
    have hnat : (795809647 : ℕ)^4581*6250000000000^3557 ≤ 1907402900277^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795809647 2000000000 1907402900277 6250000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(850824009/2000000000 : ℝ), (4544980159/10000000000 : ℝ), (795809647/2000000000 : ℝ)] ![(8315538268919/25000000000000 : ℝ), (36219400508883/100000000000000 : ℝ), (1907402900277/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(850824009/2000000000 : ℝ)|^4581 ≤ (8315538268919/25000000000000 : ℝ)^3557
        have hw : |(850824009/2000000000 : ℝ)|=(850824009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4544980159/10000000000 : ℝ)|^4581 ≤ (36219400508883/100000000000000 : ℝ)^3557
        have hw : |(4544980159/10000000000 : ℝ)|=(4544980159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(795809647/2000000000 : ℝ)|^4581 ≤ (1907402900277/6250000000000 : ℝ)^3557
        have hw : |(795809647/2000000000 : ℝ)|=(795809647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1542_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10651/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15893/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8741/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8741/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8741/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8741/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8741/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8741/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8741/100000 : ℝ) ^ (4579/1024 : ℝ) ≤ (924635077861893/50000000000000000000 : ℝ) := by
    have hpowers : (8741/100000 : ℝ)^4579 ≤ (924635077861893/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8741 : ℕ)^4579*50000000000000000000^1024 ≤ 924635077861893^1024*100000^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8741 100000 924635077861893 50000000000000000000 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8741/100000 : ℝ)) (X := (924635077861893/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18021/100000 : ℝ) ^ (4579/1024 : ℝ) ≤ (46998236733062179/100000000000000000000 : ℝ) := by
    have hpowers : (18021/100000 : ℝ)^4579 ≤ (46998236733062179/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18021 : ℕ)^4579*100000000000000000000^1024 ≤ 46998236733062179^1024*100000^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18021 100000 46998236733062179 100000000000000000000 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18021/100000 : ℝ)) (X := (46998236733062179/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000924635077861893/25000000000000000000 : ℝ) ≤ (5000041354563279/5000000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (25000924635077861893/25000000000000000000 : ℝ)^1024 ≤ (5000041354563279/5000000000000000 : ℝ)^4579 := by
      have hnat : (25000924635077861893 : ℕ)^1024*5000000000000000^4579 ≤ 5000041354563279^4579*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000924635077861893 25000000000000000000 5000041354563279 5000000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000041354563279/5000000000000000 : ℝ)) (X := (25000924635077861893/25000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009769501377757193/20000000000000000000 : ℝ) ≤ (10001092167833451/10000000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (20009769501377757193/20000000000000000000 : ℝ)^1024 ≤ (10001092167833451/10000000000000000 : ℝ)^4579 := by
      have hnat : (20009769501377757193 : ℕ)^1024*10000000000000000^4579 ≤ 10001092167833451^4579*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009769501377757193 20000000000000000000 10001092167833451 10000000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001092167833451/10000000000000000 : ℝ)) (X := (20009769501377757193/20000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50046998236733062179/50000000000000000000 : ℝ) ≤ (1250262703317543/1250000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (50046998236733062179/50000000000000000000 : ℝ)^1024 ≤ (1250262703317543/1250000000000000 : ℝ)^4579 := by
      have hnat : (50046998236733062179 : ℕ)^1024*1250000000000000^4579 ≤ 1250262703317543^4579*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50046998236733062179 50000000000000000000 1250262703317543 1250000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250262703317543/1250000000000000 : ℝ)) (X := (50046998236733062179/50000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(924635077861893/50000000000000000000 : ℝ) ≤ ((46391560091790277407/46400000000000000000 : ℝ)+2*(1009458706893/928000000000000 : ℝ)*(8741/100000 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (46391560091790277407/46400000000000000000 : ℝ)+2*(1009458706893/928000000000000 : ℝ)*(8741/100000 : ℝ)=(5000041354563279/5000000000000000 : ℝ) by norm_num, show 1+2*(924635077861893/50000000000000000000 : ℝ)=(25000924635077861893/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46998236733062179/100000000000000000000 : ℝ)+(924635077861893/50000000000000000000 : ℝ) ≤ ((46391560091790277407/46400000000000000000 : ℝ)+(1009458706893/928000000000000 : ℝ)*((18021/100000 : ℝ)+(8741/100000 : ℝ)))^(4579/1024 : ℝ) := by
    rw [show (46391560091790277407/46400000000000000000 : ℝ)+(1009458706893/928000000000000 : ℝ)*((18021/100000 : ℝ)+(8741/100000 : ℝ))=(10001092167833451/10000000000000000 : ℝ) by norm_num, show 1+(46998236733062179/100000000000000000000 : ℝ)+(924635077861893/50000000000000000000 : ℝ)=(20009769501377757193/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46998236733062179/100000000000000000000 : ℝ) ≤ ((46391560091790277407/46400000000000000000 : ℝ)+2*(1009458706893/928000000000000 : ℝ)*(18021/100000 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (46391560091790277407/46400000000000000000 : ℝ)+2*(1009458706893/928000000000000 : ℝ)*(18021/100000 : ℝ)=(1250262703317543/1250000000000000 : ℝ) by norm_num, show 1+2*(46998236733062179/100000000000000000000 : ℝ)=(50046998236733062179/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46391560091790277407/46400000000000000000 : ℝ)*(X 1 0+X 2 0)+(1009458706893/928000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (8741/100000 : ℝ)) (hi := (18021/100000 : ℝ)) (c := (46391560091790277407/46400000000000000000 : ℝ)) (alpha := (1009458706893/928000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46391560091790277407/46400000000000000000 : ℝ)*(X 0 1+X 2 1)+(1009458706893/928000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (8741/100000 : ℝ)) (hi := (18021/100000 : ℝ)) (c := (46391560091790277407/46400000000000000000 : ℝ)) (alpha := (1009458706893/928000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46391560091790277407/46400000000000000000 : ℝ)*(X 0 2+X 1 2)+(1009458706893/928000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (8741/100000 : ℝ)) (hi := (18021/100000 : ℝ)) (c := (46391560091790277407/46400000000000000000 : ℝ)) (alpha := (1009458706893/928000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1821534617/10000000000 : ℝ)*X 0 0+(1362226163/2500000000 : ℝ)*X 0 1+(5201481927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354995553/10000000000 : ℝ)*X 1 0+(-1948693207/10000000000 : ℝ)*X 1 1+(1300370569/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677498127/5000000000 : ℝ)*X 2 0+(2600740907/5000000000 : ℝ)*X 2 1+(-1948692881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4254015441/10000000000 : ℝ)*X 0 0+(993883039/2500000000 : ℝ)*X 0 1+(4548465991/10000000000 : ℝ)*X 0 2+(4254015441/10000000000 : ℝ)*X 1 0+(993883039/2500000000 : ℝ)*X 1 1+(4548465991/10000000000 : ℝ)*X 1 2+(4254015441/10000000000 : ℝ)*X 2 0+(993883039/2500000000 : ℝ)*X 2 1+(4548465991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-364315827/2000000000 : ℝ)*X 0 0+(2601493653/5000000000 : ℝ)*X 0 1+(5447386681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644878109/5000000000 : ℝ)*X 1 0+(-851394313/5000000000 : ℝ)*X 1 1+(272369339/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289756239/10000000000 : ℝ)*X 2 0+(340461691/625000000 : ℝ)*X 2 1+(-170278821/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((850824009/2000000000 : ℝ)*X 0 0+(4544980159/10000000000 : ℝ)*X 0 1+(795809647/2000000000 : ℝ)*X 0 2+(850824009/2000000000 : ℝ)*X 1 0+(4544980159/10000000000 : ℝ)*X 1 1+(795809647/2000000000 : ℝ)*X 1 2+(850824009/2000000000 : ℝ)*X 2 0+(4544980159/10000000000 : ℝ)*X 2 1+(795809647/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1639595788362261460130812653/290000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1456743949/100000000000000 : ℝ)*(base19) + (1634169589/100000000000000 : ℝ)*(base23) + (138278899/100000000000000 : ℝ)*(upper3) + (23539083/12500000000000 : ℝ)*(upper4) + (64663213/25000000000000 : ℝ)*(upper5) + (723392534439193/25000000000000 : ℝ)*(major0) + (723392534439193/25000000000000 : ℝ)*(major1) + (723392534439193/25000000000000 : ℝ)*(major2) + (1010421289503289/25000000000000 : ℝ)*(sp0) + (1010428060174019/25000000000000 : ℝ)*(sp1) + (1010428015817609/25000000000000 : ℝ)*(sp2) + (1745413837899051/100000000000000 : ℝ)*(sp3) + (28539426869/100000000000000 : ℝ)*(sp4) + (1568964397/12500000000000 : ℝ)*(sp7) + (1745426389614227/100000000000000 : ℝ)*(f.failure) + (505214212180003/12500000000000 : ℝ)*(f.sum) + (19528939733051/11600000000000000000000000000 : ℝ)*base66 + (10109317887049337449/1160000000000000000000000000000000 : ℝ)*base68 + (2556317579190662551/1160000000000000000000000000000000 : ℝ)*base69 + (3147573099729337449/1160000000000000000000000000000000 : ℝ)*base72 + (9036392444549/11600000000000000000000000000 : ℝ)*base73 + (3812529687809337449/1160000000000000000000000000000000 : ℝ)*base76 + (6818273290289337449/1160000000000000000000000000000000 : ℝ)*base78 + (9517630049529337449/1160000000000000000000000000000000 : ℝ)*base80 + (71439734151349/11600000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (190951/1000000000000000000000 : ℝ)*base89 + (190951/1000000000000000000000 : ℝ)*base91 + (190951/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15389284188535897324028428221/1160000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1647713607/100000000000000 : ℝ)*(base19) + (405629819/20000000000000 : ℝ)*(base23) + (45307917/20000000000000 : ℝ)*(upper3) + (123387817/100000000000000 : ℝ)*(lower4) + (106087849/50000000000000 : ℝ)*(upper5) + (1464664773076001/50000000000000 : ℝ)*(major0) + (1464664773076001/50000000000000 : ℝ)*(major1) + (1464664773076001/50000000000000 : ℝ)*(major2) + (4588026119/20000000000000 : ℝ)*(sp1) + (33556197397/100000000000000 : ℝ)*(sp2) + (2045830938910517/50000000000000 : ℝ)*(sp4) + (3995739540993/97656250000 : ℝ)*(sp5) + (2045813146737271/50000000000000 : ℝ)*(sp6) + (883498386131077/50000000000000 : ℝ)*(sp7) + (883498386131077/50000000000000 : ℝ)*(f.failure) + (2045830938910517/50000000000000 : ℝ)*(f.sum) + (163792359513107/23200000000000000000000000000 : ℝ)*base66 + (10357520369571140593/2320000000000000000000000000000000 : ℝ)*base68 + (5783059102851140593/2320000000000000000000000000000000 : ℝ)*base70 + (30654192215891140593/2320000000000000000000000000000000 : ℝ)*base72 + (58148146969907/23200000000000000000000000000 : ℝ)*base74 + (16842353396828859407/2320000000000000000000000000000000 : ℝ)*base75 + (19841908694691140593/2320000000000000000000000000000000 : ℝ)*base78 + (8192800344508859407/2320000000000000000000000000000000 : ℝ)*base79 + (54424457046707/23200000000000000000000000000 : ℝ)*base82 + (4210001/500000000000000000000 : ℝ)*base89 + (4210001/500000000000000000000 : ℝ)*base91 + (4210001/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1542_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8741/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10651/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15893/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1542_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1542_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10651/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15893/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1542_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1542_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1542_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10651/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15893/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1542_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

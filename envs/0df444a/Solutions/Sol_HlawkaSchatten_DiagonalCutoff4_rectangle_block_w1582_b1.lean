-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1582_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:30:42.859224+00:00
-- url     : https://prove2.me/submissions/00de544d-c7cc-4428-9a8f-688f8d4845f5

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
theorem support_rectangle_w1582_s3_0 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1769134467/10000000000 : ℝ)*x 0 + (271286307/500000000 : ℝ)*x 1 + (652392563/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1769134467/10000000000 : ℝ)^4661 ≤ (5431719888397/50000000000000 : ℝ)^3637 := by
    have hnat : (1769134467 : ℕ)^4661*50000000000000^3637 ≤ 5431719888397^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769134467 10000000000 5431719888397 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271286307/500000000 : ℝ)^4661 ≤ (45676654660639/100000000000000 : ℝ)^3637 := by
    have hnat : (271286307 : ℕ)^4661*100000000000000^3637 ≤ 45676654660639^3637*500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271286307 500000000 45676654660639 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652392563/1250000000 : ℝ)^4661 ≤ (10864976386193/25000000000000 : ℝ)^3637 := by
    have hnat : (652392563 : ℕ)^4661*25000000000000^3637 ≤ 10864976386193^3637*1250000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652392563 1250000000 10864976386193 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1769134467/10000000000 : ℝ), (271286307/500000000 : ℝ), (652392563/1250000000 : ℝ)] ![(5431719888397/50000000000000 : ℝ), (45676654660639/100000000000000 : ℝ), (10864976386193/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1769134467/10000000000 : ℝ)|^4661 ≤ (5431719888397/50000000000000 : ℝ)^3637
        have hw : |(-1769134467/10000000000 : ℝ)|=(1769134467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271286307/500000000 : ℝ)|^4661 ≤ (45676654660639/100000000000000 : ℝ)^3637
        have hw : |(271286307/500000000 : ℝ)|=(271286307/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652392563/1250000000 : ℝ)|^4661 ≤ (10864976386193/25000000000000 : ℝ)^3637
        have hw : |(652392563/1250000000 : ℝ)|=(652392563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s3_1 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347833659/10000000000 : ℝ)*x 0 + (-58588441/312500000 : ℝ)*x 1 + (2609570241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347833659/10000000000 : ℝ)^4661 ≤ (2802374642999/6250000000000 : ℝ)^3637 := by
    have hnat : (5347833659 : ℕ)^4661*6250000000000^3637 ≤ 2802374642999^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347833659 10000000000 2802374642999 6250000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58588441/312500000 : ℝ)^4661 ≤ (182845318411/1562500000000 : ℝ)^3637 := by
    have hnat : (58588441 : ℕ)^4661*1562500000000^3637 ≤ 182845318411^3637*312500000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58588441 312500000 182845318411 1562500000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609570241/5000000000 : ℝ)^4661 ≤ (43459905309999/100000000000000 : ℝ)^3637 := by
    have hnat : (2609570241 : ℕ)^4661*100000000000000^3637 ≤ 43459905309999^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609570241 5000000000 43459905309999 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347833659/10000000000 : ℝ), (-58588441/312500000 : ℝ), (2609570241/5000000000 : ℝ)] ![(2802374642999/6250000000000 : ℝ), (182845318411/1562500000000 : ℝ), (43459905309999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347833659/10000000000 : ℝ)|^4661 ≤ (2802374642999/6250000000000 : ℝ)^3637
        have hw : |(5347833659/10000000000 : ℝ)|=(5347833659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-58588441/312500000 : ℝ)|^4661 ≤ (182845318411/1562500000000 : ℝ)^3637
        have hw : |(-58588441/312500000 : ℝ)|=(58588441/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609570241/5000000000 : ℝ)|^4661 ≤ (43459905309999/100000000000000 : ℝ)^3637
        have hw : |(2609570241/5000000000 : ℝ)|=(2609570241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s3_2 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10695667/20000000 : ℝ)*x 0 + (2609570303/5000000000 : ℝ)*x 1 + (-937415081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10695667/20000000 : ℝ)^4661 ≤ (22418996289769/50000000000000 : ℝ)^3637 := by
    have hnat : (10695667 : ℕ)^4661*50000000000000^3637 ≤ 22418996289769^3637*20000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10695667 20000000 22418996289769 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609570303/5000000000 : ℝ)^4661 ≤ (21729953316633/50000000000000 : ℝ)^3637 := by
    have hnat : (2609570303 : ℕ)^4661*50000000000000^3637 ≤ 21729953316633^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609570303 5000000000 21729953316633 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937415081/5000000000 : ℝ)^4661 ≤ (731381298641/6250000000000 : ℝ)^3637 := by
    have hnat : (937415081 : ℕ)^4661*6250000000000^3637 ≤ 731381298641^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937415081 5000000000 731381298641 6250000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10695667/20000000 : ℝ), (2609570303/5000000000 : ℝ), (-937415081/5000000000 : ℝ)] ![(22418996289769/50000000000000 : ℝ), (21729953316633/50000000000000 : ℝ), (731381298641/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10695667/20000000 : ℝ)|^4661 ≤ (22418996289769/50000000000000 : ℝ)^3637
        have hw : |(10695667/20000000 : ℝ)|=(10695667/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609570303/5000000000 : ℝ)|^4661 ≤ (21729953316633/50000000000000 : ℝ)^3637
        have hw : |(2609570303/5000000000 : ℝ)|=(2609570303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-937415081/5000000000 : ℝ)|^4661 ≤ (731381298641/6250000000000 : ℝ)^3637
        have hw : |(-937415081/5000000000 : ℝ)|=(937415081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s3_3 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4238114821/10000000000 : ℝ)*x 0 + (999502321/2500000000 : ℝ)*x 1 + (4489656683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4238114821/10000000000 : ℝ)^4661 ≤ (8320375654833/25000000000000 : ℝ)^3637 := by
    have hnat : (4238114821 : ℕ)^4661*25000000000000^3637 ≤ 8320375654833^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238114821 10000000000 8320375654833 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999502321/2500000000 : ℝ)^4661 ≤ (7721161531421/25000000000000 : ℝ)^3637 := by
    have hnat : (999502321 : ℕ)^4661*25000000000000^3637 ≤ 7721161531421^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999502321 2500000000 7721161531421 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489656683/10000000000 : ℝ)^4661 ≤ (7166770248949/20000000000000 : ℝ)^3637 := by
    have hnat : (4489656683 : ℕ)^4661*20000000000000^3637 ≤ 7166770248949^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489656683 10000000000 7166770248949 20000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4238114821/10000000000 : ℝ), (999502321/2500000000 : ℝ), (4489656683/10000000000 : ℝ)] ![(8320375654833/25000000000000 : ℝ), (7721161531421/25000000000000 : ℝ), (7166770248949/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4238114821/10000000000 : ℝ)|^4661 ≤ (8320375654833/25000000000000 : ℝ)^3637
        have hw : |(4238114821/10000000000 : ℝ)|=(4238114821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(999502321/2500000000 : ℝ)|^4661 ≤ (7721161531421/25000000000000 : ℝ)^3637
        have hw : |(999502321/2500000000 : ℝ)|=(999502321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489656683/10000000000 : ℝ)|^4661 ≤ (7166770248949/20000000000000 : ℝ)^3637
        have hw : |(4489656683/10000000000 : ℝ)|=(4489656683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s3_4 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-442290493/2500000000 : ℝ)*x 0 + (208809353/400000000 : ℝ)*x 1 + (2712312289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442290493/2500000000 : ℝ)^4661 ≤ (10863656225463/100000000000000 : ℝ)^3637 := by
    have hnat : (442290493 : ℕ)^4661*100000000000000^3637 ≤ 10863656225463^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442290493 2500000000 10863656225463 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208809353/400000000 : ℝ)^4661 ≤ (43471573267173/100000000000000 : ℝ)^3637 := by
    have hnat : (208809353 : ℕ)^4661*100000000000000^3637 ≤ 43471573267173^3637*400000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208809353 400000000 43471573267173 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712312289/5000000000 : ℝ)^4661 ≤ (2283238524671/5000000000000 : ℝ)^3637 := by
    have hnat : (2712312289 : ℕ)^4661*5000000000000^3637 ≤ 2283238524671^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712312289 5000000000 2283238524671 5000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442290493/2500000000 : ℝ), (208809353/400000000 : ℝ), (2712312289/5000000000 : ℝ)] ![(10863656225463/100000000000000 : ℝ), (43471573267173/100000000000000 : ℝ), (2283238524671/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442290493/2500000000 : ℝ)|^4661 ≤ (10863656225463/100000000000000 : ℝ)^3637
        have hw : |(-442290493/2500000000 : ℝ)|=(442290493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208809353/400000000 : ℝ)|^4661 ≤ (43471573267173/100000000000000 : ℝ)^3637
        have hw : |(208809353/400000000 : ℝ)|=(208809353/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712312289/5000000000 : ℝ)|^4661 ≤ (2283238524671/5000000000000 : ℝ)^3637
        have hw : |(2712312289/5000000000 : ℝ)|=(2712312289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s3_5 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264655027/500000000 : ℝ)*x 0 + (-834673039/5000000000 : ℝ)*x 1 + (542462499/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264655027/500000000 : ℝ)^4661 ≤ (22125369749087/50000000000000 : ℝ)^3637 := by
    have hnat : (264655027 : ℕ)^4661*50000000000000^3637 ≤ 22125369749087^3637*500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264655027 500000000 22125369749087 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834673039/5000000000 : ℝ)^4661 ≤ (10084485555843/100000000000000 : ℝ)^3637 := by
    have hnat : (834673039 : ℕ)^4661*100000000000000^3637 ≤ 10084485555843^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834673039 5000000000 10084485555843 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542462499/1000000000 : ℝ)^4661 ≤ (45664774938143/100000000000000 : ℝ)^3637 := by
    have hnat : (542462499 : ℕ)^4661*100000000000000^3637 ≤ 45664774938143^3637*1000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542462499 1000000000 45664774938143 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264655027/500000000 : ℝ), (-834673039/5000000000 : ℝ), (542462499/1000000000 : ℝ)] ![(22125369749087/50000000000000 : ℝ), (10084485555843/100000000000000 : ℝ), (45664774938143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264655027/500000000 : ℝ)|^4661 ≤ (22125369749087/50000000000000 : ℝ)^3637
        have hw : |(264655027/500000000 : ℝ)|=(264655027/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-834673039/5000000000 : ℝ)|^4661 ≤ (10084485555843/100000000000000 : ℝ)^3637
        have hw : |(-834673039/5000000000 : ℝ)|=(834673039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542462499/1000000000 : ℝ)|^4661 ≤ (45664774938143/100000000000000 : ℝ)^3637
        have hw : |(542462499/1000000000 : ℝ)|=(542462499/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s3_6 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293100867/10000000000 : ℝ)*x 0 + (135615613/250000000 : ℝ)*x 1 + (-1669346281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293100867/10000000000 : ℝ)^4661 ≤ (5531342875201/12500000000000 : ℝ)^3637 := by
    have hnat : (5293100867 : ℕ)^4661*12500000000000^3637 ≤ 5531342875201^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293100867 10000000000 5531342875201 12500000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135615613/250000000 : ℝ)^4661 ≤ (45664769867707/100000000000000 : ℝ)^3637 := by
    have hnat : (135615613 : ℕ)^4661*100000000000000^3637 ≤ 45664769867707^3637*250000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135615613 250000000 45664769867707 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1669346281/10000000000 : ℝ)^4661 ≤ (10084487127433/100000000000000 : ℝ)^3637 := by
    have hnat : (1669346281 : ℕ)^4661*100000000000000^3637 ≤ 10084487127433^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669346281 10000000000 10084487127433 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293100867/10000000000 : ℝ), (135615613/250000000 : ℝ), (-1669346281/10000000000 : ℝ)] ![(5531342875201/12500000000000 : ℝ), (45664769867707/100000000000000 : ℝ), (10084487127433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293100867/10000000000 : ℝ)|^4661 ≤ (5531342875201/12500000000000 : ℝ)^3637
        have hw : |(5293100867/10000000000 : ℝ)|=(5293100867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135615613/250000000 : ℝ)|^4661 ≤ (45664769867707/100000000000000 : ℝ)^3637
        have hw : |(135615613/250000000 : ℝ)|=(135615613/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1669346281/10000000000 : ℝ)|^4661 ≤ (10084487127433/100000000000000 : ℝ)^3637
        have hw : |(-1669346281/10000000000 : ℝ)|=(1669346281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s3_7 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059544967/2500000000 : ℝ)*x 0 + (2243527433/5000000000 : ℝ)*x 1 + (4000630877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059544967/2500000000 : ℝ)^4661 ≤ (4160269655849/12500000000000 : ℝ)^3637 := by
    have hnat : (1059544967 : ℕ)^4661*12500000000000^3637 ≤ 4160269655849^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059544967 2500000000 4160269655849 12500000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243527433/5000000000 : ℝ)^4661 ≤ (35807240473217/100000000000000 : ℝ)^3637 := by
    have hnat : (2243527433 : ℕ)^4661*100000000000000^3637 ≤ 35807240473217^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243527433 5000000000 35807240473217 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4000630877/10000000000 : ℝ)^4661 ≤ (30910602258243/100000000000000 : ℝ)^3637 := by
    have hnat : (4000630877 : ℕ)^4661*100000000000000^3637 ≤ 30910602258243^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4000630877 10000000000 30910602258243 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059544967/2500000000 : ℝ), (2243527433/5000000000 : ℝ), (4000630877/10000000000 : ℝ)] ![(4160269655849/12500000000000 : ℝ), (35807240473217/100000000000000 : ℝ), (30910602258243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059544967/2500000000 : ℝ)|^4661 ≤ (4160269655849/12500000000000 : ℝ)^3637
        have hw : |(1059544967/2500000000 : ℝ)|=(1059544967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243527433/5000000000 : ℝ)|^4661 ≤ (35807240473217/100000000000000 : ℝ)^3637
        have hw : |(2243527433/5000000000 : ℝ)|=(2243527433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4000630877/10000000000 : ℝ)|^4661 ≤ (30910602258243/100000000000000 : ℝ)^3637
        have hw : |(4000630877/10000000000 : ℝ)|=(4000630877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1582_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2177/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11131/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7757/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2177/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2177/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2177/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2177/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2177/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2177/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2177/20000 : ℝ) ^ (4659/1024 : ℝ) ≤ (4147223982687157/100000000000000000000 : ℝ) := by
    have hpowers : (2177/20000 : ℝ)^4659 ≤ (4147223982687157/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2177 : ℕ)^4659*100000000000000000000^1024 ≤ 4147223982687157^1024*20000^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2177 20000 4147223982687157 100000000000000000000 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2177/20000 : ℝ)) (X := (4147223982687157/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15781/100000 : ℝ) ^ (4659/1024 : ℝ) ≤ (11236697355654561/50000000000000000000 : ℝ) := by
    have hpowers : (15781/100000 : ℝ)^4659 ≤ (11236697355654561/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15781 : ℕ)^4659*50000000000000000000^1024 ≤ 11236697355654561^1024*100000^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15781 100000 11236697355654561 50000000000000000000 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15781/100000 : ℝ)) (X := (11236697355654561/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004147223982687157/50000000000000000000 : ℝ) ≤ (10000182297486689/10000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (50004147223982687157/50000000000000000000 : ℝ)^1024 ≤ (10000182297486689/10000000000000000 : ℝ)^4659 := by
      have hnat : (50004147223982687157 : ℕ)^1024*10000000000000000^4659 ≤ 10000182297486689^4659*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004147223982687157 50000000000000000000 10000182297486689 10000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000182297486689/10000000000000000 : ℝ)) (X := (50004147223982687157/50000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026620618693996279/100000000000000000000 : ℝ) ≤ (10000585032906903/10000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (100026620618693996279/100000000000000000000 : ℝ)^1024 ≤ (10000585032906903/10000000000000000 : ℝ)^4659 := by
      have hnat : (100026620618693996279 : ℕ)^1024*10000000000000000^4659 ≤ 10000585032906903^4659*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026620618693996279 100000000000000000000 10000585032906903 10000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000585032906903/10000000000000000 : ℝ)) (X := (100026620618693996279/100000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011236697355654561/25000000000000000000 : ℝ) ≤ (10000987768327117/10000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (25011236697355654561/25000000000000000000 : ℝ)^1024 ≤ (10000987768327117/10000000000000000 : ℝ)^4659 := by
      have hnat : (25011236697355654561 : ℕ)^1024*10000000000000000^4659 ≤ 10000987768327117^4659*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011236697355654561 25000000000000000000 10000987768327117 10000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000987768327117/10000000000000000 : ℝ)) (X := (25011236697355654561/25000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4147223982687157/100000000000000000000 : ℝ) ≤ ((12238031244599192641/12240000000000000000 : ℝ)+2*(201367710107/244800000000000 : ℝ)*(2177/20000 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (12238031244599192641/12240000000000000000 : ℝ)+2*(201367710107/244800000000000 : ℝ)*(2177/20000 : ℝ)=(10000182297486689/10000000000000000 : ℝ) by norm_num, show 1+2*(4147223982687157/100000000000000000000 : ℝ)=(50004147223982687157/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11236697355654561/50000000000000000000 : ℝ)+(4147223982687157/100000000000000000000 : ℝ) ≤ ((12238031244599192641/12240000000000000000 : ℝ)+(201367710107/244800000000000 : ℝ)*((15781/100000 : ℝ)+(2177/20000 : ℝ)))^(4659/1024 : ℝ) := by
    rw [show (12238031244599192641/12240000000000000000 : ℝ)+(201367710107/244800000000000 : ℝ)*((15781/100000 : ℝ)+(2177/20000 : ℝ))=(10000585032906903/10000000000000000 : ℝ) by norm_num, show 1+(11236697355654561/50000000000000000000 : ℝ)+(4147223982687157/100000000000000000000 : ℝ)=(100026620618693996279/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11236697355654561/50000000000000000000 : ℝ) ≤ ((12238031244599192641/12240000000000000000 : ℝ)+2*(201367710107/244800000000000 : ℝ)*(15781/100000 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (12238031244599192641/12240000000000000000 : ℝ)+2*(201367710107/244800000000000 : ℝ)*(15781/100000 : ℝ)=(10000987768327117/10000000000000000 : ℝ) by norm_num, show 1+2*(11236697355654561/50000000000000000000 : ℝ)=(25011236697355654561/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12238031244599192641/12240000000000000000 : ℝ)*(X 1 0+X 2 0)+(201367710107/244800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (2177/20000 : ℝ)) (hi := (15781/100000 : ℝ)) (c := (12238031244599192641/12240000000000000000 : ℝ)) (alpha := (201367710107/244800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12238031244599192641/12240000000000000000 : ℝ)*(X 0 1+X 2 1)+(201367710107/244800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (2177/20000 : ℝ)) (hi := (15781/100000 : ℝ)) (c := (12238031244599192641/12240000000000000000 : ℝ)) (alpha := (201367710107/244800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12238031244599192641/12240000000000000000 : ℝ)*(X 0 2+X 1 2)+(201367710107/244800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (2177/20000 : ℝ)) (hi := (15781/100000 : ℝ)) (c := (12238031244599192641/12240000000000000000 : ℝ)) (alpha := (201367710107/244800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1769134467/10000000000 : ℝ)*X 0 0+(271286307/500000000 : ℝ)*X 0 1+(652392563/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347833659/10000000000 : ℝ)*X 1 0+(-58588441/312500000 : ℝ)*X 1 1+(2609570241/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((10695667/20000000 : ℝ)*X 2 0+(2609570303/5000000000 : ℝ)*X 2 1+(-937415081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4238114821/10000000000 : ℝ)*X 0 0+(999502321/2500000000 : ℝ)*X 0 1+(4489656683/10000000000 : ℝ)*X 0 2+(4238114821/10000000000 : ℝ)*X 1 0+(999502321/2500000000 : ℝ)*X 1 1+(4489656683/10000000000 : ℝ)*X 1 2+(4238114821/10000000000 : ℝ)*X 2 0+(999502321/2500000000 : ℝ)*X 2 1+(4489656683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-442290493/2500000000 : ℝ)*X 0 0+(208809353/400000000 : ℝ)*X 0 1+(2712312289/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((264655027/500000000 : ℝ)*X 1 0+(-834673039/5000000000 : ℝ)*X 1 1+(542462499/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293100867/10000000000 : ℝ)*X 2 0+(135615613/250000000 : ℝ)*X 2 1+(-1669346281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1059544967/2500000000 : ℝ)*X 0 0+(2243527433/5000000000 : ℝ)*X 0 1+(4000630877/10000000000 : ℝ)*X 0 2+(1059544967/2500000000 : ℝ)*X 1 0+(2243527433/5000000000 : ℝ)*X 1 1+(4000630877/10000000000 : ℝ)*X 1 2+(1059544967/2500000000 : ℝ)*X 2 0+(2243527433/5000000000 : ℝ)*X 2 1+(4000630877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (383746208729442774647052059/34000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (551946101/25000000000000 : ℝ)*(base19) + (444805839/25000000000000 : ℝ)*(base23) + (19027573/12500000000000 : ℝ)*(lower2) + (393557227/100000000000000 : ℝ)*(upper3) + (58539781/50000000000000 : ℝ)*(upper5) + (1718671378643301/50000000000000 : ℝ)*(major0) + (1718671378643301/50000000000000 : ℝ)*(major1) + (1718671378643301/50000000000000 : ℝ)*(major2) + (4840645331779731/100000000000000 : ℝ)*(sp0) + (2420337410038313/50000000000000 : ℝ)*(sp1) + (2420337624318837/50000000000000 : ℝ)*(sp2) + (2033991223858757/100000000000000 : ℝ)*(sp3) + (31696081299/100000000000000 : ℝ)*(sp4) + (1688663163/10000000000000 : ℝ)*(sp7) + (2034008110490387/100000000000000 : ℝ)*(f.failure) + (484067702786103/10000000000000 : ℝ)*(f.sum) + (8954346023789/2040000000000000000000000000 : ℝ)*base65 + (342604846295832647/204000000000000000000000000000000 : ℝ)*base67 + (2189205664679832647/204000000000000000000000000000000 : ℝ)*base69 + (2699478395543832647/204000000000000000000000000000000 : ℝ)*base71 + (4681905709171/2040000000000000000000000000 : ℝ)*base74 + (1824314437535832647/204000000000000000000000000000000 : ℝ)*base75 + (4148424204479832647/204000000000000000000000000000000 : ℝ)*base77 + (1493943426779832647/204000000000000000000000000000000 : ℝ)*base79 + (2801446900949/2040000000000000000000000000 : ℝ)*base81 + (67055753/5000000000000000000000 : ℝ)*base90 + (67055753/5000000000000000000000 : ℝ)*base92 + (67055753/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (102732460342091142653/13600000000000000000000000 : ℝ) := by norm_num
    linear_combination (730725833/100000000000000 : ℝ)*(base19) + (553937049/50000000000000 : ℝ)*(base23) + (9589467/5000000000000 : ℝ)*(upper3) + (23268177/50000000000000 : ℝ)*(lower4) + (135927317/100000000000000 : ℝ)*(upper5) + (34742044496729/1000000000000 : ℝ)*(major0) + (34742044496729/1000000000000 : ℝ)*(major1) + (34742044496729/1000000000000 : ℝ)*(major2) + (3349349917/20000000000000 : ℝ)*(sp1) + (7743516151/50000000000000 : ℝ)*(sp2) + (611573506727641/12500000000000 : ℝ)*(sp4) + (489257057634571/10000000000000 : ℝ)*(sp5) + (611571432364341/12500000000000 : ℝ)*(sp6) + (2055820593729423/100000000000000 : ℝ)*(sp7) + (2055820593729423/100000000000000 : ℝ)*(f.failure) + (611573506727641/12500000000000 : ℝ)*(f.sum) + (166040310239/612000000000000000000000000 : ℝ)*base65 + (1828588089201289/12240000000000000000000000000000 : ℝ)*base67 + (2849552603678711/12240000000000000000000000000000 : ℝ)*base70 + (46422032441438711/12240000000000000000000000000000 : ℝ)*base72 + (1838463928199/612000000000000000000000000 : ℝ)*base73 + (63601298631681289/12240000000000000000000000000000 : ℝ)*base75 + (89734756676078711/12240000000000000000000000000000 : ℝ)*base78 + (38370728991921289/12240000000000000000000000000000 : ℝ)*base79 + (1116927518867/612000000000000000000000000 : ℝ)*base81 + (28487363/5000000000000000000000 : ℝ)*base89 + (28487363/5000000000000000000000 : ℝ)*base91 + (28487363/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1582_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2177/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7757/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1582_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1582_s4_0 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1769330797/10000000000 : ℝ)*x 0 + (1084881571/2000000000 : ℝ)*x 1 + (1305082103/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1769330797/10000000000 : ℝ)^4661 ≤ (10864984802717/100000000000000 : ℝ)^3637 := by
    have hnat : (1769330797 : ℕ)^4661*100000000000000^3637 ≤ 10864984802717^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769330797 10000000000 10864984802717 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084881571/2000000000 : ℝ)^4661 ≤ (4566243246409/10000000000000 : ℝ)^3637 := by
    have hnat : (1084881571 : ℕ)^4661*10000000000000^3637 ≤ 4566243246409^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084881571 2000000000 4566243246409 10000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305082103/2500000000 : ℝ)^4661 ≤ (10868145678683/25000000000000 : ℝ)^3637 := by
    have hnat : (1305082103 : ℕ)^4661*25000000000000^3637 ≤ 10868145678683^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305082103 2500000000 10868145678683 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1769330797/10000000000 : ℝ), (1084881571/2000000000 : ℝ), (1305082103/2500000000 : ℝ)] ![(10864984802717/100000000000000 : ℝ), (4566243246409/10000000000000 : ℝ), (10868145678683/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1769330797/10000000000 : ℝ)|^4661 ≤ (10864984802717/100000000000000 : ℝ)^3637
        have hw : |(-1769330797/10000000000 : ℝ)|=(1769330797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084881571/2000000000 : ℝ)|^4661 ≤ (4566243246409/10000000000000 : ℝ)^3637
        have hw : |(1084881571/2000000000 : ℝ)|=(1084881571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305082103/2500000000 : ℝ)|^4661 ≤ (10868145678683/25000000000000 : ℝ)^3637
        have hw : |(1305082103/2500000000 : ℝ)|=(1305082103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s4_1 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069496693/2000000000 : ℝ)*x 0 + (-117107221/625000000 : ℝ)*x 1 + (1305082107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069496693/2000000000 : ℝ)^4661 ≤ (22417115754169/50000000000000 : ℝ)^3637 := by
    have hnat : (1069496693 : ℕ)^4661*50000000000000^3637 ≤ 22417115754169^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069496693 2000000000 22417115754169 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117107221/625000000 : ℝ)^4661 ≤ (1169318558999/10000000000000 : ℝ)^3637 := by
    have hnat : (117107221 : ℕ)^4661*10000000000000^3637 ≤ 1169318558999^3637*625000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117107221 625000000 1169318558999 10000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305082107/2500000000 : ℝ)^4661 ≤ (43472582885487/100000000000000 : ℝ)^3637 := by
    have hnat : (1305082107 : ℕ)^4661*100000000000000^3637 ≤ 43472582885487^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305082107 2500000000 43472582885487 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069496693/2000000000 : ℝ), (-117107221/625000000 : ℝ), (1305082107/2500000000 : ℝ)] ![(22417115754169/50000000000000 : ℝ), (1169318558999/10000000000000 : ℝ), (43472582885487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069496693/2000000000 : ℝ)|^4661 ≤ (22417115754169/50000000000000 : ℝ)^3637
        have hw : |(1069496693/2000000000 : ℝ)|=(1069496693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117107221/625000000 : ℝ)|^4661 ≤ (1169318558999/10000000000000 : ℝ)^3637
        have hw : |(-117107221/625000000 : ℝ)|=(117107221/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305082107/2500000000 : ℝ)|^4661 ≤ (43472582885487/100000000000000 : ℝ)^3637
        have hw : |(1305082107/2500000000 : ℝ)|=(1305082107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s4_2 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534748347/1000000000 : ℝ)*x 0 + (5220328423/10000000000 : ℝ)*x 1 + (-117107221/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534748347/1000000000 : ℝ)^4661 ≤ (22417115781031/50000000000000 : ℝ)^3637 := by
    have hnat : (534748347 : ℕ)^4661*50000000000000^3637 ≤ 22417115781031^3637*1000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534748347 1000000000 22417115781031 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220328423/10000000000 : ℝ)^4661 ≤ (21736291416063/50000000000000 : ℝ)^3637 := by
    have hnat : (5220328423 : ℕ)^4661*50000000000000^3637 ≤ 21736291416063^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220328423 10000000000 21736291416063 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117107221/625000000 : ℝ)^4661 ≤ (1169318558999/10000000000000 : ℝ)^3637 := by
    have hnat : (117107221 : ℕ)^4661*10000000000000^3637 ≤ 1169318558999^3637*625000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117107221 625000000 1169318558999 10000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534748347/1000000000 : ℝ), (5220328423/10000000000 : ℝ), (-117107221/625000000 : ℝ)] ![(22417115781031/50000000000000 : ℝ), (21736291416063/50000000000000 : ℝ), (1169318558999/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534748347/1000000000 : ℝ)|^4661 ≤ (22417115781031/50000000000000 : ℝ)^3637
        have hw : |(534748347/1000000000 : ℝ)|=(534748347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220328423/10000000000 : ℝ)|^4661 ≤ (21736291416063/50000000000000 : ℝ)^3637
        have hw : |(5220328423/10000000000 : ℝ)|=(5220328423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-117107221/625000000 : ℝ)|^4661 ≤ (1169318558999/10000000000000 : ℝ)^3637
        have hw : |(-117107221/625000000 : ℝ)|=(117107221/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s4_3 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4238238619/10000000000 : ℝ)*x 0 + (2000489061/5000000000 : ℝ)*x 1 + (4486660837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4238238619/10000000000 : ℝ)^4661 ≤ (8320687128569/25000000000000 : ℝ)^3637 := by
    have hnat : (4238238619 : ℕ)^4661*25000000000000^3637 ≤ 8320687128569^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238238619 10000000000 8320687128569 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000489061/5000000000 : ℝ)^4661 ≤ (30914040655833/100000000000000 : ℝ)^3637 := by
    have hnat : (2000489061 : ℕ)^4661*100000000000000^3637 ≤ 30914040655833^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000489061 5000000000 30914040655833 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486660837/10000000000 : ℝ)^4661 ≤ (2237700676007/6250000000000 : ℝ)^3637 := by
    have hnat : (4486660837 : ℕ)^4661*6250000000000^3637 ≤ 2237700676007^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486660837 10000000000 2237700676007 6250000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4238238619/10000000000 : ℝ), (2000489061/5000000000 : ℝ), (4486660837/10000000000 : ℝ)] ![(8320687128569/25000000000000 : ℝ), (30914040655833/100000000000000 : ℝ), (2237700676007/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4238238619/10000000000 : ℝ)|^4661 ≤ (8320687128569/25000000000000 : ℝ)^3637
        have hw : |(4238238619/10000000000 : ℝ)|=(4238238619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2000489061/5000000000 : ℝ)|^4661 ≤ (30914040655833/100000000000000 : ℝ)^3637
        have hw : |(2000489061/5000000000 : ℝ)|=(2000489061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486660837/10000000000 : ℝ)|^4661 ≤ (2237700676007/6250000000000 : ℝ)^3637
        have hw : |(4486660837/10000000000 : ℝ)|=(4486660837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s4_4 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1769357257/10000000000 : ℝ)*x 0 + (5221395423/10000000000 : ℝ)*x 1 + (5423332941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1769357257/10000000000 : ℝ)^4661 ≤ (135814912929/1250000000000 : ℝ)^3637 := by
    have hnat : (1769357257 : ℕ)^4661*1250000000000^3637 ≤ 135814912929^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769357257 10000000000 135814912929 1250000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221395423/10000000000 : ℝ)^4661 ≤ (434839703831/1000000000000 : ℝ)^3637 := by
    have hnat : (5221395423 : ℕ)^4661*1000000000000^3637 ≤ 434839703831^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221395423 10000000000 434839703831 1000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423332941/10000000000 : ℝ)^4661 ≤ (2853177285839/6250000000000 : ℝ)^3637 := by
    have hnat : (5423332941 : ℕ)^4661*6250000000000^3637 ≤ 2853177285839^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423332941 10000000000 2853177285839 6250000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1769357257/10000000000 : ℝ), (5221395423/10000000000 : ℝ), (5423332941/10000000000 : ℝ)] ![(135814912929/1250000000000 : ℝ), (434839703831/1000000000000 : ℝ), (2853177285839/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1769357257/10000000000 : ℝ)|^4661 ≤ (135814912929/1250000000000 : ℝ)^3637
        have hw : |(-1769357257/10000000000 : ℝ)|=(1769357257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221395423/10000000000 : ℝ)|^4661 ≤ (434839703831/1000000000000 : ℝ)^3637
        have hw : |(5221395423/10000000000 : ℝ)|=(5221395423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423332941/10000000000 : ℝ)|^4661 ≤ (2853177285839/6250000000000 : ℝ)^3637
        have hw : |(5423332941/10000000000 : ℝ)|=(5423332941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s4_5 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293415143/10000000000 : ℝ)*x 0 + (-334142197/2000000000 : ℝ)*x 1 + (1355833227/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293415143/10000000000 : ℝ)^4661 ≤ (8850822028123/20000000000000 : ℝ)^3637 := by
    have hnat : (5293415143 : ℕ)^4661*20000000000000^3637 ≤ 8850822028123^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293415143 10000000000 8850822028123 20000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (334142197/2000000000 : ℝ)^4661 ≤ (10095053638603/100000000000000 : ℝ)^3637 := by
    have hnat : (334142197 : ℕ)^4661*100000000000000^3637 ≤ 10095053638603^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334142197 2000000000 10095053638603 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355833227/2500000000 : ℝ)^4661 ≤ (45650836217439/100000000000000 : ℝ)^3637 := by
    have hnat : (1355833227 : ℕ)^4661*100000000000000^3637 ≤ 45650836217439^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355833227 2500000000 45650836217439 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293415143/10000000000 : ℝ), (-334142197/2000000000 : ℝ), (1355833227/2500000000 : ℝ)] ![(8850822028123/20000000000000 : ℝ), (10095053638603/100000000000000 : ℝ), (45650836217439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293415143/10000000000 : ℝ)|^4661 ≤ (8850822028123/20000000000000 : ℝ)^3637
        have hw : |(5293415143/10000000000 : ℝ)|=(5293415143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-334142197/2000000000 : ℝ)|^4661 ≤ (10095053638603/100000000000000 : ℝ)^3637
        have hw : |(-334142197/2000000000 : ℝ)|=(334142197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355833227/2500000000 : ℝ)|^4661 ≤ (45650836217439/100000000000000 : ℝ)^3637
        have hw : |(1355833227/2500000000 : ℝ)|=(1355833227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s4_6 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293415107/10000000000 : ℝ)*x 0 + (1084666581/2000000000 : ℝ)*x 1 + (-835355519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293415107/10000000000 : ℝ)^4661 ≤ (44254109754909/100000000000000 : ℝ)^3637 := by
    have hnat : (5293415107 : ℕ)^4661*100000000000000^3637 ≤ 44254109754909^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293415107 10000000000 44254109754909 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084666581/2000000000 : ℝ)^4661 ≤ (11412709046269/25000000000000 : ℝ)^3637 := by
    have hnat : (1084666581 : ℕ)^4661*25000000000000^3637 ≤ 11412709046269^3637*2000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084666581 2000000000 11412709046269 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (835355519/5000000000 : ℝ)^4661 ≤ (5047527024507/50000000000000 : ℝ)^3637 := by
    have hnat : (835355519 : ℕ)^4661*50000000000000^3637 ≤ 5047527024507^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835355519 5000000000 5047527024507 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293415107/10000000000 : ℝ), (1084666581/2000000000 : ℝ), (-835355519/5000000000 : ℝ)] ![(44254109754909/100000000000000 : ℝ), (11412709046269/25000000000000 : ℝ), (5047527024507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293415107/10000000000 : ℝ)|^4661 ≤ (44254109754909/100000000000000 : ℝ)^3637
        have hw : |(5293415107/10000000000 : ℝ)|=(5293415107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084666581/2000000000 : ℝ)|^4661 ≤ (11412709046269/25000000000000 : ℝ)^3637
        have hw : |(1084666581/2000000000 : ℝ)|=(1084666581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-835355519/5000000000 : ℝ)|^4661 ≤ (5047527024507/50000000000000 : ℝ)^3637
        have hw : |(-835355519/5000000000 : ℝ)|=(835355519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s4_7 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4238301571/10000000000 : ℝ)*x 0 + (4484121493/10000000000 : ℝ)*x 1 + (1000884073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4238301571/10000000000 : ℝ)^4661 ≤ (16641691031501/50000000000000 : ℝ)^3637 := by
    have hnat : (4238301571 : ℕ)^4661*50000000000000^3637 ≤ 16641691031501^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238301571 10000000000 16641691031501 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484121493/10000000000 : ℝ)^4661 ≤ (35777243834769/100000000000000 : ℝ)^3637 := by
    have hnat : (4484121493 : ℕ)^4661*100000000000000^3637 ≤ 35777243834769^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484121493 10000000000 35777243834769 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000884073/2500000000 : ℝ)^4661 ≤ (15469687039677/50000000000000 : ℝ)^3637 := by
    have hnat : (1000884073 : ℕ)^4661*50000000000000^3637 ≤ 15469687039677^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000884073 2500000000 15469687039677 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4238301571/10000000000 : ℝ), (4484121493/10000000000 : ℝ), (1000884073/2500000000 : ℝ)] ![(16641691031501/50000000000000 : ℝ), (35777243834769/100000000000000 : ℝ), (15469687039677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4238301571/10000000000 : ℝ)|^4661 ≤ (16641691031501/50000000000000 : ℝ)^3637
        have hw : |(4238301571/10000000000 : ℝ)|=(4238301571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484121493/10000000000 : ℝ)|^4661 ≤ (35777243834769/100000000000000 : ℝ)^3637
        have hw : |(4484121493/10000000000 : ℝ)|=(4484121493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1000884073/2500000000 : ℝ)|^4661 ≤ (15469687039677/50000000000000 : ℝ)^3637
        have hw : |(1000884073/2500000000 : ℝ)|=(1000884073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1582_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7757/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11157/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7743/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7757/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7757/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7757/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7757/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7757/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7757/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11131/100000 : ℝ) ^ (4659/1024 : ℝ) ≤ (4591100031226449/100000000000000000000 : ℝ) := by
    have hpowers : (11131/100000 : ℝ)^4659 ≤ (4591100031226449/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11131 : ℕ)^4659*100000000000000000000^1024 ≤ 4591100031226449^1024*100000^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11131 100000 4591100031226449 100000000000000000000 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11131/100000 : ℝ)) (X := (4591100031226449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7757/50000 : ℝ) ^ (4659/1024 : ℝ) ≤ (20794634585051561/100000000000000000000 : ℝ) := by
    have hpowers : (7757/50000 : ℝ)^4659 ≤ (20794634585051561/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7757 : ℕ)^4659*100000000000000000000^1024 ≤ 20794634585051561^1024*50000^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7757 50000 20794634585051561 100000000000000000000 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7757/50000 : ℝ)) (X := (20794634585051561/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004591100031226449/50000000000000000000 : ℝ) ≤ (10000201808029189/10000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (50004591100031226449/50000000000000000000 : ℝ)^1024 ≤ (10000201808029189/10000000000000000 : ℝ)^4659 := by
      have hnat : (50004591100031226449 : ℕ)^1024*10000000000000000^4659 ≤ 10000201808029189^4659*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004591100031226449 50000000000000000000 10000201808029189 10000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000201808029189/10000000000000000 : ℝ)) (X := (50004591100031226449/50000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002538573461627801/10000000000000000000 : ℝ) ≤ (5000278948468803/5000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (10002538573461627801/10000000000000000000 : ℝ)^1024 ≤ (5000278948468803/5000000000000000 : ℝ)^4659 := by
      have hnat : (10002538573461627801 : ℕ)^1024*5000000000000000^4659 ≤ 5000278948468803^4659*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002538573461627801 10000000000000000000 5000278948468803 5000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000278948468803/5000000000000000 : ℝ)) (X := (10002538573461627801/10000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020794634585051561/50000000000000000000 : ℝ) ≤ (10000913985846023/10000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (50020794634585051561/50000000000000000000 : ℝ)^1024 ≤ (10000913985846023/10000000000000000 : ℝ)^4659 := by
      have hnat : (50020794634585051561 : ℕ)^1024*10000000000000000^4659 ≤ 10000913985846023^4659*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020794634585051561 50000000000000000000 10000913985846023 10000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000913985846023/10000000000000000 : ℝ)) (X := (50020794634585051561/50000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4591100031226449/100000000000000000000 : ℝ) ≤ ((43822957273312756133/43830000000000000000 : ℝ)+2*(356088908417/438300000000000 : ℝ)*(11131/100000 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (43822957273312756133/43830000000000000000 : ℝ)+2*(356088908417/438300000000000 : ℝ)*(11131/100000 : ℝ)=(10000201808029189/10000000000000000 : ℝ) by norm_num, show 1+2*(4591100031226449/100000000000000000000 : ℝ)=(50004591100031226449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20794634585051561/100000000000000000000 : ℝ)+(4591100031226449/100000000000000000000 : ℝ) ≤ ((43822957273312756133/43830000000000000000 : ℝ)+(356088908417/438300000000000 : ℝ)*((7757/50000 : ℝ)+(11131/100000 : ℝ)))^(4659/1024 : ℝ) := by
    rw [show (43822957273312756133/43830000000000000000 : ℝ)+(356088908417/438300000000000 : ℝ)*((7757/50000 : ℝ)+(11131/100000 : ℝ))=(5000278948468803/5000000000000000 : ℝ) by norm_num, show 1+(20794634585051561/100000000000000000000 : ℝ)+(4591100031226449/100000000000000000000 : ℝ)=(10002538573461627801/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20794634585051561/100000000000000000000 : ℝ) ≤ ((43822957273312756133/43830000000000000000 : ℝ)+2*(356088908417/438300000000000 : ℝ)*(7757/50000 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (43822957273312756133/43830000000000000000 : ℝ)+2*(356088908417/438300000000000 : ℝ)*(7757/50000 : ℝ)=(10000913985846023/10000000000000000 : ℝ) by norm_num, show 1+2*(20794634585051561/100000000000000000000 : ℝ)=(50020794634585051561/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43822957273312756133/43830000000000000000 : ℝ)*(X 1 0+X 2 0)+(356088908417/438300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (7757/50000 : ℝ)) (c := (43822957273312756133/43830000000000000000 : ℝ)) (alpha := (356088908417/438300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43822957273312756133/43830000000000000000 : ℝ)*(X 0 1+X 2 1)+(356088908417/438300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (7757/50000 : ℝ)) (c := (43822957273312756133/43830000000000000000 : ℝ)) (alpha := (356088908417/438300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43822957273312756133/43830000000000000000 : ℝ)*(X 0 2+X 1 2)+(356088908417/438300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (7757/50000 : ℝ)) (c := (43822957273312756133/43830000000000000000 : ℝ)) (alpha := (356088908417/438300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1769330797/10000000000 : ℝ)*X 0 0+(1084881571/2000000000 : ℝ)*X 0 1+(1305082103/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069496693/2000000000 : ℝ)*X 1 0+(-117107221/625000000 : ℝ)*X 1 1+(1305082107/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534748347/1000000000 : ℝ)*X 2 0+(5220328423/10000000000 : ℝ)*X 2 1+(-117107221/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4238238619/10000000000 : ℝ)*X 0 0+(2000489061/5000000000 : ℝ)*X 0 1+(4486660837/10000000000 : ℝ)*X 0 2+(4238238619/10000000000 : ℝ)*X 1 0+(2000489061/5000000000 : ℝ)*X 1 1+(4486660837/10000000000 : ℝ)*X 1 2+(4238238619/10000000000 : ℝ)*X 2 0+(2000489061/5000000000 : ℝ)*X 2 1+(4486660837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1769357257/10000000000 : ℝ)*X 0 0+(5221395423/10000000000 : ℝ)*X 0 1+(5423332941/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293415143/10000000000 : ℝ)*X 1 0+(-334142197/2000000000 : ℝ)*X 1 1+(1355833227/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293415107/10000000000 : ℝ)*X 2 0+(1084666581/2000000000 : ℝ)*X 2 1+(-835355519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4238301571/10000000000 : ℝ)*X 0 0+(4484121493/10000000000 : ℝ)*X 0 1+(1000884073/2500000000 : ℝ)*X 0 2+(4238301571/10000000000 : ℝ)*X 1 0+(4484121493/10000000000 : ℝ)*X 1 1+(1000884073/2500000000 : ℝ)*X 1 2+(4238301571/10000000000 : ℝ)*X 2 0+(4484121493/10000000000 : ℝ)*X 2 1+(1000884073/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (273965155166247969603243793/45656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1005940233/100000000000000 : ℝ)*(base19) + (948753853/100000000000000 : ℝ)*(base23) + (8257591/25000000000000 : ℝ)*(lower2) + (29685419/20000000000000 : ℝ)*(upper3) + (26210961/25000000000000 : ℝ)*(upper5) + (217470568186271/6250000000000 : ℝ)*(major0) + (217470568186271/6250000000000 : ℝ)*(major1) + (217470568186271/6250000000000 : ℝ)*(major2) + (2450034916824219/50000000000000 : ℝ)*(sp0) + (4900085586912449/100000000000000 : ℝ)*(sp1) + (1225021411024707/25000000000000 : ℝ)*(sp2) + (1029481998342841/50000000000000 : ℝ)*(sp3) + (4189801061/25000000000000 : ℝ)*(sp4) + (1848100527/25000000000000 : ℝ)*(sp7) + (205897138908779/10000000000000 : ℝ)*(f.failure) + (4900086592852681/100000000000000 : ℝ)*(f.sum) + (10987186558979/2739375000000000000000000000 : ℝ)*base65 + (816680545098274957/273937500000000000000000000000000 : ℝ)*base68 + (905970275988274957/273937500000000000000000000000000 : ℝ)*base70 + (5487112099616537543/273937500000000000000000000000000 : ℝ)*base71 + (262264074793/342421875000000000000000000 : ℝ)*base73 + (2636920555044274957/273937500000000000000000000000000 : ℝ)*base76 + (4296520177452475043/273937500000000000000000000000000 : ℝ)*base77 + (1060466440822399957/273937500000000000000000000000000 : ℝ)*base80 + (27871382466559/10957500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1859601/500000000000000000000 : ℝ)*base90 + (1859601/500000000000000000000 : ℝ)*base92 + (1859601/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (772695289947280674502139093/365250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (433951077/100000000000000 : ℝ)*(base19) + (395143839/100000000000000 : ℝ)*(base23) + (36843933/100000000000000 : ℝ)*(upper3) + (3027359/50000000000000 : ℝ)*(lower4) + (2623621/5000000000000 : ℝ)*(upper5) + (1758205782980293/50000000000000 : ℝ)*(major0) + (1758205782980293/50000000000000 : ℝ)*(major1) + (1758205782980293/50000000000000 : ℝ)*(major2) + (1432671247/20000000000000 : ℝ)*(sp1) + (138534621/2500000000000 : ℝ)*(sp2) + (990405378243101/20000000000000 : ℝ)*(sp4) + (4952019293908193/100000000000000 : ℝ)*(sp5) + (2476010477343413/50000000000000 : ℝ)*(sp6) + (2080796170188179/100000000000000 : ℝ)*(sp7) + (2080796170188179/100000000000000 : ℝ)*(f.failure) + (990405378243101/20000000000000 : ℝ)*(f.sum) + (45757832187701/10957500000000000000000000000 : ℝ)*base65 + (14226070580198986969/2191500000000000000000000000000000 : ℝ)*base67 + (12594986195692486969/2191500000000000000000000000000000 : ℝ)*base69 + (11814138068377486969/2191500000000000000000000000000000 : ℝ)*base71 + (19135267237021/2739375000000000000000000000 : ℝ)*base74 + (37374685149653986969/2191500000000000000000000000000000 : ℝ)*base75 + (5314687502395486969/2191500000000000000000000000000000 : ℝ)*base77 + (27954759070696486969/2191500000000000000000000000000000 : ℝ)*base79 + (67136996826619/10957500000000000000000000000 : ℝ)*base82 + (10248201/5000000000000000000000 : ℝ)*base90 + (10248201/5000000000000000000000 : ℝ)*base92 + (10248201/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1582_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7757/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11157/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1582_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1582_s5_0 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1769350039/10000000000 : ℝ)*x 0 + (5424277273/10000000000 : ℝ)*x 1 + (2610223111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1769350039/10000000000 : ℝ)^4661 ≤ (5432568115459/50000000000000 : ℝ)^3637 := by
    have hnat : (1769350039 : ℕ)^4661*50000000000000^3637 ≤ 5432568115459^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769350039 10000000000 5432568115459 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424277273/10000000000 : ℝ)^4661 ≤ (45661023745153/100000000000000 : ℝ)^3637 := by
    have hnat : (5424277273 : ℕ)^4661*100000000000000^3637 ≤ 45661023745153^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424277273 10000000000 45661023745153 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610223111/5000000000 : ℝ)^4661 ≤ (1358557500283/3125000000000 : ℝ)^3637 := by
    have hnat : (2610223111 : ℕ)^4661*3125000000000^3637 ≤ 1358557500283^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610223111 5000000000 1358557500283 3125000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1769350039/10000000000 : ℝ), (5424277273/10000000000 : ℝ), (2610223111/5000000000 : ℝ)] ![(5432568115459/50000000000000 : ℝ), (45661023745153/100000000000000 : ℝ), (1358557500283/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1769350039/10000000000 : ℝ)|^4661 ≤ (5432568115459/50000000000000 : ℝ)^3637
        have hw : |(-1769350039/10000000000 : ℝ)|=(1769350039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424277273/10000000000 : ℝ)|^4661 ≤ (45661023745153/100000000000000 : ℝ)^3637
        have hw : |(5424277273/10000000000 : ℝ)|=(5424277273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610223111/5000000000 : ℝ)|^4661 ≤ (1358557500283/3125000000000 : ℝ)^3637
        have hw : |(2610223111/5000000000 : ℝ)|=(2610223111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s5_1 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336862209/2500000000 : ℝ)*x 0 + (-23420061/125000000 : ℝ)*x 1 + (652555777/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336862209/2500000000 : ℝ)^4661 ≤ (4483385942893/10000000000000 : ℝ)^3637 := by
    have hnat : (1336862209 : ℕ)^4661*10000000000000^3637 ≤ 4483385942893^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336862209 2500000000 4483385942893 10000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23420061/125000000 : ℝ)^4661 ≤ (5846150302053/50000000000000 : ℝ)^3637 := by
    have hnat : (23420061 : ℕ)^4661*50000000000000^3637 ≤ 5846150302053^3637*125000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23420061 125000000 5846150302053 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652555777/1250000000 : ℝ)^4661 ≤ (21736919972511/50000000000000 : ℝ)^3637 := by
    have hnat : (652555777 : ℕ)^4661*50000000000000^3637 ≤ 21736919972511^3637*1250000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652555777 1250000000 21736919972511 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336862209/2500000000 : ℝ), (-23420061/125000000 : ℝ), (652555777/1250000000 : ℝ)] ![(4483385942893/10000000000000 : ℝ), (5846150302053/50000000000000 : ℝ), (21736919972511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336862209/2500000000 : ℝ)|^4661 ≤ (4483385942893/10000000000000 : ℝ)^3637
        have hw : |(1336862209/2500000000 : ℝ)|=(1336862209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23420061/125000000 : ℝ)|^4661 ≤ (5846150302053/50000000000000 : ℝ)^3637
        have hw : |(-23420061/125000000 : ℝ)|=(23420061/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652555777/1250000000 : ℝ)|^4661 ≤ (21736919972511/50000000000000 : ℝ)^3637
        have hw : |(652555777/1250000000 : ℝ)|=(652555777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s5_2 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347448823/10000000000 : ℝ)*x 0 + (1305111553/2500000000 : ℝ)*x 1 + (-1873604903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347448823/10000000000 : ℝ)^4661 ≤ (1401058102789/3125000000000 : ℝ)^3637 := by
    have hnat : (5347448823 : ℕ)^4661*3125000000000^3637 ≤ 1401058102789^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347448823 10000000000 1401058102789 3125000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305111553/2500000000 : ℝ)^4661 ≤ (43473839902333/100000000000000 : ℝ)^3637 := by
    have hnat : (1305111553 : ℕ)^4661*100000000000000^3637 ≤ 43473839902333^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305111553 2500000000 43473839902333 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873604903/10000000000 : ℝ)^4661 ≤ (233846015761/2000000000000 : ℝ)^3637 := by
    have hnat : (1873604903 : ℕ)^4661*2000000000000^3637 ≤ 233846015761^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873604903 10000000000 233846015761 2000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347448823/10000000000 : ℝ), (1305111553/2500000000 : ℝ), (-1873604903/10000000000 : ℝ)] ![(1401058102789/3125000000000 : ℝ), (43473839902333/100000000000000 : ℝ), (233846015761/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347448823/10000000000 : ℝ)|^4661 ≤ (1401058102789/3125000000000 : ℝ)^3637
        have hw : |(5347448823/10000000000 : ℝ)|=(5347448823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305111553/2500000000 : ℝ)|^4661 ≤ (43473839902333/100000000000000 : ℝ)^3637
        have hw : |(1305111553/2500000000 : ℝ)|=(1305111553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1873604903/10000000000 : ℝ)|^4661 ≤ (233846015761/2000000000000 : ℝ)^3637
        have hw : |(-1873604903/10000000000 : ℝ)|=(1873604903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s5_3 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4238250871/10000000000 : ℝ)*x 0 + (2000636131/5000000000 : ℝ)*x 1 + (1121590993/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4238250871/10000000000 : ℝ)^4661 ≤ (33282871818157/100000000000000 : ℝ)^3637 := by
    have hnat : (4238250871 : ℕ)^4661*100000000000000^3637 ≤ 33282871818157^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238250871 10000000000 33282871818157 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000636131/5000000000 : ℝ)^4661 ≤ (7729238319217/25000000000000 : ℝ)^3637 := by
    have hnat : (2000636131 : ℕ)^4661*25000000000000^3637 ≤ 7729238319217^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000636131 5000000000 7729238319217 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121590993/2500000000 : ℝ)^4661 ≤ (17900087450971/50000000000000 : ℝ)^3637 := by
    have hnat : (1121590993 : ℕ)^4661*50000000000000^3637 ≤ 17900087450971^3637*2500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121590993 2500000000 17900087450971 50000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4238250871/10000000000 : ℝ), (2000636131/5000000000 : ℝ), (1121590993/2500000000 : ℝ)] ![(33282871818157/100000000000000 : ℝ), (7729238319217/25000000000000 : ℝ), (17900087450971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4238250871/10000000000 : ℝ)|^4661 ≤ (33282871818157/100000000000000 : ℝ)^3637
        have hw : |(4238250871/10000000000 : ℝ)|=(4238250871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2000636131/5000000000 : ℝ)|^4661 ≤ (7729238319217/25000000000000 : ℝ)^3637
        have hw : |(2000636131/5000000000 : ℝ)|=(2000636131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121590993/2500000000 : ℝ)|^4661 ≤ (17900087450971/50000000000000 : ℝ)^3637
        have hw : |(1121590993/2500000000 : ℝ)|=(1121590993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s5_4 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1769376381/10000000000 : ℝ)*x 0 + (326344413/625000000 : ℝ)*x 1 + (5423205027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1769376381/10000000000 : ℝ)^4661 ≤ (2716335883633/25000000000000 : ℝ)^3637 := by
    have hnat : (1769376381 : ℕ)^4661*25000000000000^3637 ≤ 2716335883633^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769376381 10000000000 2716335883633 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326344413/625000000 : ℝ)^4661 ≤ (43485199733493/100000000000000 : ℝ)^3637 := by
    have hnat : (326344413 : ℕ)^4661*100000000000000^3637 ≤ 43485199733493^3637*625000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326344413 625000000 43485199733493 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423205027/10000000000 : ℝ)^4661 ≤ (45649456713779/100000000000000 : ℝ)^3637 := by
    have hnat : (5423205027 : ℕ)^4661*100000000000000^3637 ≤ 45649456713779^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423205027 10000000000 45649456713779 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1769376381/10000000000 : ℝ), (326344413/625000000 : ℝ), (5423205027/10000000000 : ℝ)] ![(2716335883633/25000000000000 : ℝ), (43485199733493/100000000000000 : ℝ), (45649456713779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1769376381/10000000000 : ℝ)|^4661 ≤ (2716335883633/25000000000000 : ℝ)^3637
        have hw : |(-1769376381/10000000000 : ℝ)|=(1769376381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326344413/625000000 : ℝ)|^4661 ≤ (43485199733493/100000000000000 : ℝ)^3637
        have hw : |(326344413/625000000 : ℝ)|=(326344413/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423205027/10000000000 : ℝ)|^4661 ≤ (45649456713779/100000000000000 : ℝ)^3637
        have hw : |(5423205027/10000000000 : ℝ)|=(5423205027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s5_5 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293446287/10000000000 : ℝ)*x 0 + (-26106971/156250000 : ℝ)*x 1 + (5423204951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293446287/10000000000 : ℝ)^4661 ≤ (44254443819103/100000000000000 : ℝ)^3637 := by
    have hnat : (5293446287 : ℕ)^4661*100000000000000^3637 ≤ 44254443819103^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293446287 10000000000 44254443819103 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26106971/156250000 : ℝ)^4661 ≤ (10096100268221/100000000000000 : ℝ)^3637 := by
    have hnat : (26106971 : ℕ)^4661*100000000000000^3637 ≤ 10096100268221^3637*156250000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26106971 156250000 10096100268221 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423204951/10000000000 : ℝ)^4661 ≤ (45649455893939/100000000000000 : ℝ)^3637 := by
    have hnat : (5423204951 : ℕ)^4661*100000000000000^3637 ≤ 45649455893939^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423204951 10000000000 45649455893939 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293446287/10000000000 : ℝ), (-26106971/156250000 : ℝ), (5423204951/10000000000 : ℝ)] ![(44254443819103/100000000000000 : ℝ), (10096100268221/100000000000000 : ℝ), (45649455893939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293446287/10000000000 : ℝ)|^4661 ≤ (44254443819103/100000000000000 : ℝ)^3637
        have hw : |(5293446287/10000000000 : ℝ)|=(5293446287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26106971/156250000 : ℝ)|^4661 ≤ (10096100268221/100000000000000 : ℝ)^3637
        have hw : |(-26106971/156250000 : ℝ)|=(26106971/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423204951/10000000000 : ℝ)|^4661 ≤ (45649455893939/100000000000000 : ℝ)^3637
        have hw : |(5423204951/10000000000 : ℝ)|=(5423204951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s5_6 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4234757/8000000 : ℝ)*x 0 + (5423205001/10000000000 : ℝ)*x 1 + (-835423063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4234757/8000000 : ℝ)^4661 ≤ (44254443422683/100000000000000 : ℝ)^3637 := by
    have hnat : (4234757 : ℕ)^4661*100000000000000^3637 ≤ 44254443422683^3637*8000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234757 8000000 44254443422683 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423205001/10000000000 : ℝ)^4661 ≤ (45649456433307/100000000000000 : ℝ)^3637 := by
    have hnat : (5423205001 : ℕ)^4661*100000000000000^3637 ≤ 45649456433307^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423205001 10000000000 45649456433307 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (835423063/5000000000 : ℝ)^4661 ≤ (10096100128833/100000000000000 : ℝ)^3637 := by
    have hnat : (835423063 : ℕ)^4661*100000000000000^3637 ≤ 10096100128833^3637*5000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835423063 5000000000 10096100128833 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4234757/8000000 : ℝ), (5423205001/10000000000 : ℝ), (-835423063/5000000000 : ℝ)] ![(44254443422683/100000000000000 : ℝ), (45649456433307/100000000000000 : ℝ), (10096100128833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4234757/8000000 : ℝ)|^4661 ≤ (44254443422683/100000000000000 : ℝ)^3637
        have hw : |(4234757/8000000 : ℝ)|=(4234757/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423205001/10000000000 : ℝ)|^4661 ≤ (45649456433307/100000000000000 : ℝ)^3637
        have hw : |(5423205001/10000000000 : ℝ)|=(5423205001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-835423063/5000000000 : ℝ)|^4661 ≤ (10096100128833/100000000000000 : ℝ)^3637
        have hw : |(-835423063/5000000000 : ℝ)|=(835423063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1582_s5_7 (p : ℝ) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4238313553/10000000000 : ℝ)*x 0 + (4483830773/10000000000 : ℝ)*x 1 + (200191213/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4238313553/10000000000 : ℝ)^4661 ≤ (33283502650111/100000000000000 : ℝ)^3637 := by
    have hnat : (4238313553 : ℕ)^4661*100000000000000^3637 ≤ 33283502650111^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238313553 10000000000 33283502650111 100000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483830773/10000000000 : ℝ)^4661 ≤ (8943567809061/25000000000000 : ℝ)^3637 := by
    have hnat : (4483830773 : ℕ)^4661*25000000000000^3637 ≤ 8943567809061^3637*10000000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483830773 10000000000 8943567809061 25000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200191213/500000000 : ℝ)^4661 ≤ (6188445219367/20000000000000 : ℝ)^3637 := by
    have hnat : (200191213 : ℕ)^4661*20000000000000^3637 ≤ 6188445219367^3637*500000000^4661 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200191213 500000000 6188445219367 20000000000000 4661 3637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4661/1024 : ℝ)) 4661 3637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4238313553/10000000000 : ℝ), (4483830773/10000000000 : ℝ), (200191213/500000000 : ℝ)] ![(33283502650111/100000000000000 : ℝ), (8943567809061/25000000000000 : ℝ), (6188445219367/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4238313553/10000000000 : ℝ)|^4661 ≤ (33283502650111/100000000000000 : ℝ)^3637
        have hw : |(4238313553/10000000000 : ℝ)|=(4238313553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483830773/10000000000 : ℝ)|^4661 ≤ (8943567809061/25000000000000 : ℝ)^3637
        have hw : |(4483830773/10000000000 : ℝ)|=(4483830773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(200191213/500000000 : ℝ)|^4661 ≤ (6188445219367/20000000000000 : ℝ)^3637
        have hw : |(200191213/500000000 : ℝ)|=(200191213/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1582_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11157/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11159/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11157/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11157/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11157/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11157/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11157/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11157/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11157/100000 : ℝ) ^ (4659/1024 : ℝ) ≤ (464009472360779/10000000000000000000 : ℝ) := by
    have hpowers : (11157/100000 : ℝ)^4659 ≤ (464009472360779/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11157 : ℕ)^4659*10000000000000000000^1024 ≤ 464009472360779^1024*100000^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11157 100000 464009472360779 10000000000000000000 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11157/100000 : ℝ)) (X := (464009472360779/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7743/50000 : ℝ) ^ (4659/1024 : ℝ) ≤ (20624423834608093/100000000000000000000 : ℝ) := by
    have hpowers : (7743/50000 : ℝ)^4659 ≤ (20624423834608093/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7743 : ℕ)^4659*100000000000000000000^1024 ≤ 20624423834608093^1024*50000^4659 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7743 50000 20624423834608093 100000000000000000000 4659 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7743/50000 : ℝ)) (X := (20624423834608093/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000464009472360779/5000000000000000000 : ℝ) ≤ (2500050990394847/2500000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (5000464009472360779/5000000000000000000 : ℝ)^1024 ≤ (2500050990394847/2500000000000000 : ℝ)^4659 := by
      have hnat : (5000464009472360779 : ℕ)^1024*2500000000000000^4659 ≤ 2500050990394847^4659*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000464009472360779 5000000000000000000 2500050990394847 2500000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500050990394847/2500000000000000 : ℝ)) (X := (5000464009472360779/5000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025264518558215883/100000000000000000000 : ℝ) ≤ (5000277616630177/5000000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (100025264518558215883/100000000000000000000 : ℝ)^1024 ≤ (5000277616630177/5000000000000000 : ℝ)^4659 := by
      have hnat : (100025264518558215883 : ℕ)^1024*5000000000000000^4659 ≤ 5000277616630177^4659*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025264518558215883 100000000000000000000 5000277616630177 5000000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000277616630177/5000000000000000 : ℝ)) (X := (100025264518558215883/100000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020624423834608093/50000000000000000000 : ℝ) ≤ (250022662623533/250000000000000 : ℝ) ^ (4659/1024 : ℝ) := by
    have hpowers : (50020624423834608093/50000000000000000000 : ℝ)^1024 ≤ (250022662623533/250000000000000 : ℝ)^4659 := by
      have hnat : (50020624423834608093 : ℕ)^1024*250000000000000^4659 ≤ 250022662623533^4659*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020624423834608093 50000000000000000000 250022662623533 250000000000000 1024 4659 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250022662623533/250000000000000 : ℝ)) (X := (50020624423834608093/50000000000000000000 : ℝ)) (by norm_num) 4659 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(464009472360779/10000000000000000000 : ℝ) ≤ ((150288349560375331/150312500000000000 : ℝ)+2*(19515093387/24050000000000 : ℝ)*(11157/100000 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (150288349560375331/150312500000000000 : ℝ)+2*(19515093387/24050000000000 : ℝ)*(11157/100000 : ℝ)=(2500050990394847/2500000000000000 : ℝ) by norm_num, show 1+2*(464009472360779/10000000000000000000 : ℝ)=(5000464009472360779/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20624423834608093/100000000000000000000 : ℝ)+(464009472360779/10000000000000000000 : ℝ) ≤ ((150288349560375331/150312500000000000 : ℝ)+(19515093387/24050000000000 : ℝ)*((7743/50000 : ℝ)+(11157/100000 : ℝ)))^(4659/1024 : ℝ) := by
    rw [show (150288349560375331/150312500000000000 : ℝ)+(19515093387/24050000000000 : ℝ)*((7743/50000 : ℝ)+(11157/100000 : ℝ))=(5000277616630177/5000000000000000 : ℝ) by norm_num, show 1+(20624423834608093/100000000000000000000 : ℝ)+(464009472360779/10000000000000000000 : ℝ)=(100025264518558215883/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20624423834608093/100000000000000000000 : ℝ) ≤ ((150288349560375331/150312500000000000 : ℝ)+2*(19515093387/24050000000000 : ℝ)*(7743/50000 : ℝ))^(4659/1024 : ℝ) := by
    rw [show (150288349560375331/150312500000000000 : ℝ)+2*(19515093387/24050000000000 : ℝ)*(7743/50000 : ℝ)=(250022662623533/250000000000000 : ℝ) by norm_num, show 1+2*(20624423834608093/100000000000000000000 : ℝ)=(50020624423834608093/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (150288349560375331/150312500000000000 : ℝ)*(X 1 0+X 2 0)+(19515093387/24050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (11157/100000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (150288349560375331/150312500000000000 : ℝ)) (alpha := (19515093387/24050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (150288349560375331/150312500000000000 : ℝ)*(X 0 1+X 2 1)+(19515093387/24050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (11157/100000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (150288349560375331/150312500000000000 : ℝ)) (alpha := (19515093387/24050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (150288349560375331/150312500000000000 : ℝ)*(X 0 2+X 1 2)+(19515093387/24050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4659/1024 : ℝ)) (lo := (11157/100000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (150288349560375331/150312500000000000 : ℝ)) (alpha := (19515093387/24050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1769350039/10000000000 : ℝ)*X 0 0+(5424277273/10000000000 : ℝ)*X 0 1+(2610223111/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336862209/2500000000 : ℝ)*X 1 0+(-23420061/125000000 : ℝ)*X 1 1+(652555777/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347448823/10000000000 : ℝ)*X 2 0+(1305111553/2500000000 : ℝ)*X 2 1+(-1873604903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4238250871/10000000000 : ℝ)*X 0 0+(2000636131/5000000000 : ℝ)*X 0 1+(1121590993/2500000000 : ℝ)*X 0 2+(4238250871/10000000000 : ℝ)*X 1 0+(2000636131/5000000000 : ℝ)*X 1 1+(1121590993/2500000000 : ℝ)*X 1 2+(4238250871/10000000000 : ℝ)*X 2 0+(2000636131/5000000000 : ℝ)*X 2 1+(1121590993/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1769376381/10000000000 : ℝ)*X 0 0+(326344413/625000000 : ℝ)*X 0 1+(5423205027/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293446287/10000000000 : ℝ)*X 1 0+(-26106971/156250000 : ℝ)*X 1 1+(5423204951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4234757/8000000 : ℝ)*X 2 0+(5423205001/10000000000 : ℝ)*X 2 1+(-835423063/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4238313553/10000000000 : ℝ)*X 0 0+(4483830773/10000000000 : ℝ)*X 0 1+(200191213/500000000 : ℝ)*X 0 2+(4238313553/10000000000 : ℝ)*X 1 0+(4483830773/10000000000 : ℝ)*X 1 1+(200191213/500000000 : ℝ)*X 1 2+(4238313553/10000000000 : ℝ)*X 2 0+(4483830773/10000000000 : ℝ)*X 2 1+(200191213/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1582_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10761512800342879617240711/939453125000000000000000000000 : ℝ) := by norm_num
    linear_combination (493241313/25000000000000 : ℝ)*(base19) + (1824360199/100000000000000 : ℝ)*(base23) + (73087879/100000000000000 : ℝ)*(lower2) + (304091153/100000000000000 : ℝ)*(upper3) + (90540193/50000000000000 : ℝ)*(upper5) + (108868478158637/3125000000000 : ℝ)*(major0) + (108868478158637/3125000000000 : ℝ)*(major1) + (108868478158637/3125000000000 : ℝ)*(major2) + (2453028676132387/50000000000000 : ℝ)*(sp0) + (4906086744376223/100000000000000 : ℝ)*(sp1) + (4906086892981277/100000000000000 : ℝ)*(sp2) + (515369685095453/25000000000000 : ℝ)*(sp3) + (15682538351/50000000000000 : ℝ)*(sp4) + (7381296699/50000000000000 : ℝ)*(sp7) + (2061493502975211/100000000000000 : ℝ)*(f.failure) + (1226522179335369/25000000000000 : ℝ)*(f.sum) + (5967409935763/1202500000000000000000000000 : ℝ)*base65 + (8514907631973987/1878906250000000000000000000000 : ℝ)*base68 + (10076391057848901/3757812500000000000000000000000 : ℝ)*base69 + (20101369579036401/3757812500000000000000000000000 : ℝ)*base71 + (2901891765113/1202500000000000000000000000 : ℝ)*base73 + (2414250735096347/469726562500000000000000000000 : ℝ)*base75 + (14444734139588427/7515625000000000000000000000000 : ℝ)*base77 + (9469985634932349/3757812500000000000000000000000 : ℝ)*base80 + (14174279115951/2405000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (52295791/5000000000000000000000 : ℝ)*base89 + (52295791/5000000000000000000000 : ℝ)*base91 + (52295791/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15359080891478329414733391/1503125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (797252491/50000000000000 : ℝ)*(base19) + (1694184197/100000000000000 : ℝ)*(base23) + (507520143/100000000000000 : ℝ)*(lower1) + (23071443/12500000000000 : ℝ)*(upper3) + (6405669/10000000000000 : ℝ)*(lower4) + (45406387/20000000000000 : ℝ)*(upper5) + (176031602145553/5000000000000 : ℝ)*(major0) + (176031602145553/5000000000000 : ℝ)*(major1) + (176031602145553/5000000000000 : ℝ)*(major2) + (1305945737/100000000000000 : ℝ)*(sp2) + (4957970156252909/100000000000000 : ℝ)*(sp4) + (2478984280873963/50000000000000 : ℝ)*(sp5) + (198318686244919/4000000000000 : ℝ)*(sp6) + (520823397241467/25000000000000 : ℝ)*(sp7) + (520823397241467/25000000000000 : ℝ)*(f.failure) + (4957970156252909/100000000000000 : ℝ)*(f.sum) + (2181142393413/481000000000000000000000000 : ℝ)*base65 + (13237448752246957/751562500000000000000000000000 : ℝ)*base68 + (4910339624328289/1503125000000000000000000000000 : ℝ)*base70 + (25872833132006291/375781250000000000000000000000 : ℝ)*base72 + (403836491967/120250000000000000000000000 : ℝ)*base73 + (9094680162557021/93945312500000000000000000000 : ℝ)*base75 + (768462275709539/1503125000000000000000000000000 : ℝ)*base78 + (4014734182671711/1503125000000000000000000000000 : ℝ)*base79 + (1312842326649/481000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8782273/1250000000000000000000 : ℝ)*base90 + (8782273/1250000000000000000000 : ℝ)*base92 + (8782273/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1582_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11157/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1582_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1582_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2177/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1582_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1582_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1582_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4659/1024 : ℝ) ≤ p) (hpb : p ≤ (4661/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84496781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2177/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1582_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

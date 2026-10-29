-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1534_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:05:37.614016+00:00
-- url     : https://prove2.me/submissions/318d871d-53ba-4dd6-a347-4dbf6395bc74

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
theorem support_rectangle_w1534_s6_0 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668792607/1250000000 : ℝ)*x 0 + (5218673981/10000000000 : ℝ)*x 1 + (-97218967/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668792607/1250000000 : ℝ)^4565 ≤ (44651263617503/100000000000000 : ℝ)^3541 := by
    have hnat : (668792607 : ℕ)^4565*100000000000000^3541 ≤ 44651263617503^3541*1250000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668792607 1250000000 44651263617503 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218673981/10000000000 : ℝ)^4565 ≤ (33781051181/78125000000 : ℝ)^3541 := by
    have hnat : (5218673981 : ℕ)^4565*78125000000^3541 ≤ 33781051181^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218673981 10000000000 33781051181 78125000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97218967/500000000 : ℝ)^4565 ≤ (12108990854083/100000000000000 : ℝ)^3541 := by
    have hnat : (97218967 : ℕ)^4565*100000000000000^3541 ≤ 12108990854083^3541*500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97218967 500000000 12108990854083 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668792607/1250000000 : ℝ), (5218673981/10000000000 : ℝ), (-97218967/500000000 : ℝ)] ![(44651263617503/100000000000000 : ℝ), (33781051181/78125000000 : ℝ), (12108990854083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668792607/1250000000 : ℝ)|^4565 ≤ (44651263617503/100000000000000 : ℝ)^3541
        have hw : |(668792607/1250000000 : ℝ)|=(668792607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218673981/10000000000 : ℝ)|^4565 ≤ (33781051181/78125000000 : ℝ)^3541
        have hw : |(5218673981/10000000000 : ℝ)|=(5218673981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97218967/500000000 : ℝ)|^4565 ≤ (12108990854083/100000000000000 : ℝ)^3541
        have hw : |(-97218967/500000000 : ℝ)|=(97218967/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s6_1 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-918013661/5000000000 : ℝ)*x 0 + (521976837/1000000000 : ℝ)*x 1 + (1085856409/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (918013661/5000000000 : ℝ)^4565 ≤ (2811544013273/25000000000000 : ℝ)^3541 := by
    have hnat : (918013661 : ℕ)^4565*25000000000000^3541 ≤ 2811544013273^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918013661 5000000000 2811544013273 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521976837/1000000000 : ℝ)^4565 ≤ (43251435732229/100000000000000 : ℝ)^3541 := by
    have hnat : (521976837 : ℕ)^4565*100000000000000^3541 ≤ 43251435732229^3541*1000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521976837 1000000000 43251435732229 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085856409/2000000000 : ℝ)^4565 ≤ (22751194099701/50000000000000 : ℝ)^3541 := by
    have hnat : (1085856409 : ℕ)^4565*50000000000000^3541 ≤ 22751194099701^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085856409 2000000000 22751194099701 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-918013661/5000000000 : ℝ), (521976837/1000000000 : ℝ), (1085856409/2000000000 : ℝ)] ![(2811544013273/25000000000000 : ℝ), (43251435732229/100000000000000 : ℝ), (22751194099701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-918013661/5000000000 : ℝ)|^4565 ≤ (2811544013273/25000000000000 : ℝ)^3541
        have hw : |(-918013661/5000000000 : ℝ)|=(918013661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521976837/1000000000 : ℝ)|^4565 ≤ (43251435732229/100000000000000 : ℝ)^3541
        have hw : |(521976837/1000000000 : ℝ)|=(521976837/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085856409/2000000000 : ℝ)|^4565 ≤ (22751194099701/50000000000000 : ℝ)^3541
        have hw : |(1085856409/2000000000 : ℝ)|=(1085856409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s6_2 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058917367/2000000000 : ℝ)*x 0 + (-1733771197/10000000000 : ℝ)*x 1 + (5429282331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058917367/2000000000 : ℝ)^4565 ≤ (8810463745453/20000000000000 : ℝ)^3541 := by
    have hnat : (1058917367 : ℕ)^4565*20000000000000^3541 ≤ 8810463745453^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058917367 2000000000 8810463745453 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1733771197/10000000000 : ℝ)^4565 ≤ (1044528996583/10000000000000 : ℝ)^3541 := by
    have hnat : (1733771197 : ℕ)^4565*10000000000000^3541 ≤ 1044528996583^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1733771197 10000000000 1044528996583 10000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429282331/10000000000 : ℝ)^4565 ≤ (45502391289503/100000000000000 : ℝ)^3541 := by
    have hnat : (5429282331 : ℕ)^4565*100000000000000^3541 ≤ 45502391289503^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429282331 10000000000 45502391289503 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058917367/2000000000 : ℝ), (-1733771197/10000000000 : ℝ), (5429282331/10000000000 : ℝ)] ![(8810463745453/20000000000000 : ℝ), (1044528996583/10000000000000 : ℝ), (45502391289503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058917367/2000000000 : ℝ)|^4565 ≤ (8810463745453/20000000000000 : ℝ)^3541
        have hw : |(1058917367/2000000000 : ℝ)|=(1058917367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1733771197/10000000000 : ℝ)|^4565 ≤ (1044528996583/10000000000000 : ℝ)^3541
        have hw : |(-1733771197/10000000000 : ℝ)|=(1733771197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429282331/10000000000 : ℝ)|^4565 ≤ (45502391289503/100000000000000 : ℝ)^3541
        have hw : |(5429282331/10000000000 : ℝ)|=(5429282331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s6_3 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294587/10000000 : ℝ)*x 0 + (2714641141/5000000000 : ℝ)*x 1 + (-1733771039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294587/10000000 : ℝ)^4565 ≤ (44052320497111/100000000000000 : ℝ)^3541 := by
    have hnat : (5294587 : ℕ)^4565*100000000000000^3541 ≤ 44052320497111^3541*10000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294587 10000000 44052320497111 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714641141/5000000000 : ℝ)^4565 ≤ (568779884501/1250000000000 : ℝ)^3541 := by
    have hnat : (2714641141 : ℕ)^4565*1250000000000^3541 ≤ 568779884501^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714641141 5000000000 568779884501 1250000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1733771039/10000000000 : ℝ)^4565 ≤ (10445288738671/100000000000000 : ℝ)^3541 := by
    have hnat : (1733771039 : ℕ)^4565*100000000000000^3541 ≤ 10445288738671^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1733771039 10000000000 10445288738671 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294587/10000000 : ℝ), (2714641141/5000000000 : ℝ), (-1733771039/10000000000 : ℝ)] ![(44052320497111/100000000000000 : ℝ), (568779884501/1250000000000 : ℝ), (10445288738671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294587/10000000 : ℝ)|^4565 ≤ (44052320497111/100000000000000 : ℝ)^3541
        have hw : |(5294587/10000000 : ℝ)|=(5294587/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714641141/5000000000 : ℝ)|^4565 ≤ (568779884501/1250000000000 : ℝ)^3541
        have hw : |(2714641141/5000000000 : ℝ)|=(2714641141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1733771039/10000000000 : ℝ)|^4565 ≤ (10445288738671/100000000000000 : ℝ)^3541
        have hw : |(-1733771039/10000000000 : ℝ)|=(1733771039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_s6_4 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4259700763/10000000000 : ℝ)*x 0 + (281668267/625000000 : ℝ)*x 1 + (4024228469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259700763/10000000000 : ℝ)^4565 ≤ (8320348564203/25000000000000 : ℝ)^3541 := by
    have hnat : (4259700763 : ℕ)^4565*25000000000000^3541 ≤ 8320348564203^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259700763 10000000000 8320348564203 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281668267/625000000 : ℝ)^4565 ≤ (715795885143/2000000000000 : ℝ)^3541 := by
    have hnat : (281668267 : ℕ)^4565*2000000000000^3541 ≤ 715795885143^3541*625000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281668267 625000000 715795885143 2000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4024228469/10000000000 : ℝ)^4565 ≤ (15464405733833/50000000000000 : ℝ)^3541 := by
    have hnat : (4024228469 : ℕ)^4565*50000000000000^3541 ≤ 15464405733833^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024228469 10000000000 15464405733833 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259700763/10000000000 : ℝ), (281668267/625000000 : ℝ), (4024228469/10000000000 : ℝ)] ![(8320348564203/25000000000000 : ℝ), (715795885143/2000000000000 : ℝ), (15464405733833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259700763/10000000000 : ℝ)|^4565 ≤ (8320348564203/25000000000000 : ℝ)^3541
        have hw : |(4259700763/10000000000 : ℝ)|=(4259700763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281668267/625000000 : ℝ)|^4565 ≤ (715795885143/2000000000000 : ℝ)^3541
        have hw : |(281668267/625000000 : ℝ)|=(281668267/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4024228469/10000000000 : ℝ)|^4565 ≤ (15464405733833/50000000000000 : ℝ)^3541
        have hw : |(4024228469/10000000000 : ℝ)|=(4024228469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1534_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5499/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5499/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5499/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5499/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5499/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5499/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5499/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5499/50000 : ℝ) ^ (4563/1024 : ℝ) ≤ (534615427874709/10000000000000000000 : ℝ) := by
    have hpowers : (5499/50000 : ℝ)^4563 ≤ (534615427874709/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5499 : ℕ)^4563*10000000000000000000^1024 ≤ 534615427874709^1024*50000^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5499 50000 534615427874709 10000000000000000000 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5499/50000 : ℝ)) (X := (534615427874709/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4563/1024 : ℝ) ≤ (24558398864126811/100000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4563 ≤ (24558398864126811/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4563*100000000000000000000^1024 ≤ 24558398864126811^1024*20000^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 24558398864126811 100000000000000000000 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (24558398864126811/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000534615427874709/5000000000000000000 : ℝ) ≤ (10000239940171051/10000000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (5000534615427874709/5000000000000000000 : ℝ)^1024 ≤ (10000239940171051/10000000000000000 : ℝ)^4563 := by
      have hnat : (5000534615427874709 : ℕ)^1024*10000000000000000^4563 ≤ 10000239940171051^4563*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000534615427874709 5000000000000000000 10000239940171051 10000000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000239940171051/10000000000000000 : ℝ)) (X := (5000534615427874709/5000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029904553142873901/100000000000000000000 : ℝ) ≤ (200013420430353/200000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (100029904553142873901/100000000000000000000 : ℝ)^1024 ≤ (200013420430353/200000000000000 : ℝ)^4563 := by
      have hnat : (100029904553142873901 : ℕ)^1024*200000000000000^4563 ≤ 200013420430353^4563*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029904553142873901 100000000000000000000 200013420430353 200000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200013420430353/200000000000000 : ℝ)) (X := (100029904553142873901/100000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024558398864126811/50000000000000000000 : ℝ) ≤ (10001102102864249/10000000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (50024558398864126811/50000000000000000000 : ℝ)^1024 ≤ (10001102102864249/10000000000000000 : ℝ)^4563 := by
      have hnat : (50024558398864126811 : ℕ)^1024*10000000000000000^4563 ≤ 10001102102864249^4563*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024558398864126811 50000000000000000000 10001102102864249 10000000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001102102864249/10000000000000000 : ℝ)) (X := (50024558398864126811/50000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(534615427874709/10000000000000000000 : ℝ) ≤ ((44861594546247714233/44870000000000000000 : ℝ)+2*(431081346599/448700000000000 : ℝ)*(5499/50000 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (44861594546247714233/44870000000000000000 : ℝ)+2*(431081346599/448700000000000 : ℝ)*(5499/50000 : ℝ)=(10000239940171051/10000000000000000 : ℝ) by norm_num, show 1+2*(534615427874709/10000000000000000000 : ℝ)=(5000534615427874709/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24558398864126811/100000000000000000000 : ℝ)+(534615427874709/10000000000000000000 : ℝ) ≤ ((44861594546247714233/44870000000000000000 : ℝ)+(431081346599/448700000000000 : ℝ)*((3097/20000 : ℝ)+(5499/50000 : ℝ)))^(4563/1024 : ℝ) := by
    rw [show (44861594546247714233/44870000000000000000 : ℝ)+(431081346599/448700000000000 : ℝ)*((3097/20000 : ℝ)+(5499/50000 : ℝ))=(200013420430353/200000000000000 : ℝ) by norm_num, show 1+(24558398864126811/100000000000000000000 : ℝ)+(534615427874709/10000000000000000000 : ℝ)=(100029904553142873901/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24558398864126811/100000000000000000000 : ℝ) ≤ ((44861594546247714233/44870000000000000000 : ℝ)+2*(431081346599/448700000000000 : ℝ)*(3097/20000 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (44861594546247714233/44870000000000000000 : ℝ)+2*(431081346599/448700000000000 : ℝ)*(3097/20000 : ℝ)=(10001102102864249/10000000000000000 : ℝ) by norm_num, show 1+2*(24558398864126811/100000000000000000000 : ℝ)=(50024558398864126811/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44861594546247714233/44870000000000000000 : ℝ)*(X 1 0+X 2 0)+(431081346599/448700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (5499/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (44861594546247714233/44870000000000000000 : ℝ)) (alpha := (431081346599/448700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44861594546247714233/44870000000000000000 : ℝ)*(X 0 1+X 2 1)+(431081346599/448700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (5499/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (44861594546247714233/44870000000000000000 : ℝ)) (alpha := (431081346599/448700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44861594546247714233/44870000000000000000 : ℝ)*(X 0 2+X 1 2)+(431081346599/448700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (5499/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (44861594546247714233/44870000000000000000 : ℝ)) (alpha := (431081346599/448700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((668792607/1250000000 : ℝ)*X 2 0+(5218673981/10000000000 : ℝ)*X 2 1+(-97218967/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-918013661/5000000000 : ℝ)*X 0 0+(521976837/1000000000 : ℝ)*X 0 1+(1085856409/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1058917367/2000000000 : ℝ)*X 1 0+(-1733771197/10000000000 : ℝ)*X 1 1+(5429282331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5294587/10000000 : ℝ)*X 2 0+(2714641141/5000000000 : ℝ)*X 2 1+(-1733771039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4259700763/10000000000 : ℝ)*X 0 0+(281668267/625000000 : ℝ)*X 0 1+(4024228469/10000000000 : ℝ)*X 0 2+(4259700763/10000000000 : ℝ)*X 1 0+(281668267/625000000 : ℝ)*X 1 1+(4024228469/10000000000 : ℝ)*X 1 2+(4259700763/10000000000 : ℝ)*X 2 0+(281668267/625000000 : ℝ)*X 2 1+(4024228469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2168260508906627637132161187/560875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50361693/4000000000000 : ℝ)*(base19) + (476947651/25000000000000 : ℝ)*(base23) + (125223383/25000000000000 : ℝ)*(lower1) + (22247217/10000000000000 : ℝ)*(upper2) + (211085103/100000000000000 : ℝ)*(upper3) + (67610741/20000000000000 : ℝ)*(upper5) + (855702115826087/25000000000000 : ℝ)*(major0) + (855702115826087/25000000000000 : ℝ)*(major1) + (855702115826087/25000000000000 : ℝ)*(major2) + (7579717173/100000000000000 : ℝ)*(sp0) + (4772934872773979/100000000000000 : ℝ)*(sp1) + (2386466806865827/50000000000000 : ℝ)*(sp2) + (2386462692633101/50000000000000 : ℝ)*(sp3) + (518170481243233/25000000000000 : ℝ)*(sp4) + (518170481243233/25000000000000 : ℝ)*(f.failure) + (4772934872773979/100000000000000 : ℝ)*(f.sum) + (35265386002739/11217500000000000000000000000 : ℝ)*base66 + (9013086738999396271/1121750000000000000000000000000000 : ℝ)*base67 + (23160729624268646271/1121750000000000000000000000000000 : ℝ)*base69 + (3153966096533396271/1121750000000000000000000000000000 : ℝ)*base71 + (40552363992871/11217500000000000000000000000 : ℝ)*base73 + (4333024577244603729/1121750000000000000000000000000000 : ℝ)*base76 + (1152630610526896271/1121750000000000000000000000000000 : ℝ)*base77 + (749239279422853729/1121750000000000000000000000000000 : ℝ)*base80 + (137134368814551/11217500000000000000000000000 : ℝ)*base81 + (9899397/2500000000000000000000 : ℝ)*base89 + (9899397/2500000000000000000000 : ℝ)*base91 + (9899397/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1534_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1534_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1534_box_0 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1626225859/10000000000 : ℝ)*x 0 + (5400458183/10000000000 : ℝ)*x 1 + (1350114399/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1626225859/10000000000 : ℝ)^4565 ≤ (4808804426123/50000000000000 : ℝ)^3541 := by
    have hnat : (1626225859 : ℕ)^4565*50000000000000^3541 ≤ 4808804426123^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1626225859 10000000000 4808804426123 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400458183/10000000000 : ℝ)^4565 ≤ (45191198734869/100000000000000 : ℝ)^3541 := by
    have hnat : (5400458183 : ℕ)^4565*100000000000000^3541 ≤ 45191198734869^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400458183 10000000000 45191198734869 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350114399/2500000000 : ℝ)^4565 ≤ (22595596201177/50000000000000 : ℝ)^3541 := by
    have hnat : (1350114399 : ℕ)^4565*50000000000000^3541 ≤ 22595596201177^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350114399 2500000000 22595596201177 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1626225859/10000000000 : ℝ), (5400458183/10000000000 : ℝ), (1350114399/2500000000 : ℝ)] ![(4808804426123/50000000000000 : ℝ), (45191198734869/100000000000000 : ℝ), (22595596201177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1626225859/10000000000 : ℝ)|^4565 ≤ (4808804426123/50000000000000 : ℝ)^3541
        have hw : |(-1626225859/10000000000 : ℝ)|=(1626225859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400458183/10000000000 : ℝ)|^4565 ≤ (45191198734869/100000000000000 : ℝ)^3541
        have hw : |(5400458183/10000000000 : ℝ)|=(5400458183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350114399/2500000000 : ℝ)|^4565 ≤ (22595596201177/50000000000000 : ℝ)^3541
        have hw : |(1350114399/2500000000 : ℝ)|=(1350114399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_box_1 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271003087/10000000000 : ℝ)*x 0 + (-902978191/5000000000 : ℝ)*x 1 + (2700229303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271003087/10000000000 : ℝ)^4565 ≤ (21899757264681/50000000000000 : ℝ)^3541 := by
    have hnat : (5271003087 : ℕ)^4565*50000000000000^3541 ≤ 21899757264681^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271003087 10000000000 21899757264681 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902978191/5000000000 : ℝ)^4565 ≤ (344040067453/3125000000000 : ℝ)^3541 := by
    have hnat : (902978191 : ℕ)^4565*3125000000000^3541 ≤ 344040067453^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902978191 5000000000 344040067453 3125000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700229303/5000000000 : ℝ)^4565 ≤ (45191203298163/100000000000000 : ℝ)^3541 := by
    have hnat : (2700229303 : ℕ)^4565*100000000000000^3541 ≤ 45191203298163^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700229303 5000000000 45191203298163 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271003087/10000000000 : ℝ), (-902978191/5000000000 : ℝ), (2700229303/5000000000 : ℝ)] ![(21899757264681/50000000000000 : ℝ), (344040067453/3125000000000 : ℝ), (45191203298163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271003087/10000000000 : ℝ)|^4565 ≤ (21899757264681/50000000000000 : ℝ)^3541
        have hw : |(5271003087/10000000000 : ℝ)|=(5271003087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-902978191/5000000000 : ℝ)|^4565 ≤ (344040067453/3125000000000 : ℝ)^3541
        have hw : |(-902978191/5000000000 : ℝ)|=(902978191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700229303/5000000000 : ℝ)|^4565 ≤ (45191203298163/100000000000000 : ℝ)^3541
        have hw : |(2700229303/5000000000 : ℝ)|=(2700229303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_box_2 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271003607/10000000000 : ℝ)*x 0 + (5400457941/10000000000 : ℝ)*x 1 + (-1805956587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271003607/10000000000 : ℝ)^4565 ≤ (21899760049931/50000000000000 : ℝ)^3541 := by
    have hnat : (5271003607 : ℕ)^4565*50000000000000^3541 ≤ 21899760049931^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271003607 10000000000 21899760049931 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400457941/10000000000 : ℝ)^4565 ≤ (4519119612419/10000000000000 : ℝ)^3541 := by
    have hnat : (5400457941 : ℕ)^4565*10000000000000^3541 ≤ 4519119612419^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400457941 10000000000 4519119612419 10000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1805956587/10000000000 : ℝ)^4565 ≤ (2752320942397/25000000000000 : ℝ)^3541 := by
    have hnat : (1805956587 : ℕ)^4565*25000000000000^3541 ≤ 2752320942397^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1805956587 10000000000 2752320942397 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271003607/10000000000 : ℝ), (5400457941/10000000000 : ℝ), (-1805956587/10000000000 : ℝ)] ![(21899760049931/50000000000000 : ℝ), (4519119612419/10000000000000 : ℝ), (2752320942397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271003607/10000000000 : ℝ)|^4565 ≤ (21899760049931/50000000000000 : ℝ)^3541
        have hw : |(5271003607/10000000000 : ℝ)|=(5271003607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400457941/10000000000 : ℝ)|^4565 ≤ (4519119612419/10000000000000 : ℝ)^3541
        have hw : |(5400457941/10000000000 : ℝ)|=(5400457941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1805956587/10000000000 : ℝ)|^4565 ≤ (2752320942397/25000000000000 : ℝ)^3541
        have hw : |(-1805956587/10000000000 : ℝ)|=(1805956587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_box_3 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (892347809/2000000000 : ℝ)*x 0 + (833085507/2000000000 : ℝ)*x 1 + (833085683/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892347809/2000000000 : ℝ)^4565 ≤ (1766511369289/5000000000000 : ℝ)^3541 := by
    have hnat : (892347809 : ℕ)^4565*5000000000000^3541 ≤ 1766511369289^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892347809 2000000000 1766511369289 5000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833085507/2000000000 : ℝ)^4565 ≤ (16167440947071/50000000000000 : ℝ)^3541 := by
    have hnat : (833085507 : ℕ)^4565*50000000000000^3541 ≤ 16167440947071^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833085507 2000000000 16167440947071 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (833085683/2000000000 : ℝ)^4565 ≤ (32334890700761/100000000000000 : ℝ)^3541 := by
    have hnat : (833085683 : ℕ)^4565*100000000000000^3541 ≤ 32334890700761^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833085683 2000000000 32334890700761 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(892347809/2000000000 : ℝ), (833085507/2000000000 : ℝ), (833085683/2000000000 : ℝ)] ![(1766511369289/5000000000000 : ℝ), (16167440947071/50000000000000 : ℝ), (32334890700761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(892347809/2000000000 : ℝ)|^4565 ≤ (1766511369289/5000000000000 : ℝ)^3541
        have hw : |(892347809/2000000000 : ℝ)|=(892347809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833085507/2000000000 : ℝ)|^4565 ≤ (16167440947071/50000000000000 : ℝ)^3541
        have hw : |(833085507/2000000000 : ℝ)|=(833085507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(833085683/2000000000 : ℝ)|^4565 ≤ (32334890700761/100000000000000 : ℝ)^3541
        have hw : |(833085683/2000000000 : ℝ)|=(833085683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_box_4 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1025597959/5000000000 : ℝ)*x 0 + (5244269797/10000000000 : ℝ)*x 1 + (163883441/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025597959/5000000000 : ℝ)^4565 ≤ (12973307828253/100000000000000 : ℝ)^3541 := by
    have hnat : (1025597959 : ℕ)^4565*100000000000000^3541 ≤ 12973307828253^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025597959 5000000000 12973307828253 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244269797/10000000000 : ℝ)^4565 ≤ (43513344395659/100000000000000 : ℝ)^3541 := by
    have hnat : (5244269797 : ℕ)^4565*100000000000000^3541 ≤ 43513344395659^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244269797 10000000000 43513344395659 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163883441/312500000 : ℝ)^4565 ≤ (43513347765139/100000000000000 : ℝ)^3541 := by
    have hnat : (163883441 : ℕ)^4565*100000000000000^3541 ≤ 43513347765139^3541*312500000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163883441 312500000 43513347765139 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1025597959/5000000000 : ℝ), (5244269797/10000000000 : ℝ), (163883441/312500000 : ℝ)] ![(12973307828253/100000000000000 : ℝ), (43513344395659/100000000000000 : ℝ), (43513347765139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1025597959/5000000000 : ℝ)|^4565 ≤ (12973307828253/100000000000000 : ℝ)^3541
        have hw : |(-1025597959/5000000000 : ℝ)|=(1025597959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244269797/10000000000 : ℝ)|^4565 ≤ (43513344395659/100000000000000 : ℝ)^3541
        have hw : |(5244269797/10000000000 : ℝ)|=(5244269797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163883441/312500000 : ℝ)|^4565 ≤ (43513347765139/100000000000000 : ℝ)^3541
        have hw : |(163883441/312500000 : ℝ)|=(163883441/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_box_5 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168111327/312500000 : ℝ)*x 0 + (-1870704299/10000000000 : ℝ)*x 1 + (5244269903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168111327/312500000 : ℝ)^4565 ≤ (4496590341721/10000000000000 : ℝ)^3541 := by
    have hnat : (168111327 : ℕ)^4565*10000000000000^3541 ≤ 4496590341721^3541*312500000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168111327 312500000 4496590341721 10000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1870704299/10000000000 : ℝ)^4565 ≤ (11520751040391/100000000000000 : ℝ)^3541 := by
    have hnat : (1870704299 : ℕ)^4565*100000000000000^3541 ≤ 11520751040391^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870704299 10000000000 11520751040391 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244269903/10000000000 : ℝ)^4565 ≤ (10878336382379/25000000000000 : ℝ)^3541 := by
    have hnat : (5244269903 : ℕ)^4565*25000000000000^3541 ≤ 10878336382379^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244269903 10000000000 10878336382379 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168111327/312500000 : ℝ), (-1870704299/10000000000 : ℝ), (5244269903/10000000000 : ℝ)] ![(4496590341721/10000000000000 : ℝ), (11520751040391/100000000000000 : ℝ), (10878336382379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168111327/312500000 : ℝ)|^4565 ≤ (4496590341721/10000000000000 : ℝ)^3541
        have hw : |(168111327/312500000 : ℝ)|=(168111327/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1870704299/10000000000 : ℝ)|^4565 ≤ (11520751040391/100000000000000 : ℝ)^3541
        have hw : |(-1870704299/10000000000 : ℝ)|=(1870704299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244269903/10000000000 : ℝ)|^4565 ≤ (10878336382379/25000000000000 : ℝ)^3541
        have hw : |(5244269903/10000000000 : ℝ)|=(5244269903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_box_6 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672445291/1250000000 : ℝ)*x 0 + (5244269833/10000000000 : ℝ)*x 1 + (-1870704577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672445291/1250000000 : ℝ)^4565 ≤ (2810368871981/6250000000000 : ℝ)^3541 := by
    have hnat : (672445291 : ℕ)^4565*6250000000000^3541 ≤ 2810368871981^3541*1250000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672445291 1250000000 2810368871981 6250000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244269833/10000000000 : ℝ)^4565 ≤ (21756672390371/50000000000000 : ℝ)^3541 := by
    have hnat : (5244269833 : ℕ)^4565*50000000000000^3541 ≤ 21756672390371^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244269833 10000000000 21756672390371 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870704577/10000000000 : ℝ)^4565 ≤ (11520753247559/100000000000000 : ℝ)^3541 := by
    have hnat : (1870704577 : ℕ)^4565*100000000000000^3541 ≤ 11520753247559^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870704577 10000000000 11520753247559 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672445291/1250000000 : ℝ), (5244269833/10000000000 : ℝ), (-1870704577/10000000000 : ℝ)] ![(2810368871981/6250000000000 : ℝ), (21756672390371/50000000000000 : ℝ), (11520753247559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672445291/1250000000 : ℝ)|^4565 ≤ (2810368871981/6250000000000 : ℝ)^3541
        have hw : |(672445291/1250000000 : ℝ)|=(672445291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244269833/10000000000 : ℝ)|^4565 ≤ (21756672390371/50000000000000 : ℝ)^3541
        have hw : |(5244269833/10000000000 : ℝ)|=(5244269833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1870704577/10000000000 : ℝ)|^4565 ≤ (11520753247559/100000000000000 : ℝ)^3541
        have hw : |(-1870704577/10000000000 : ℝ)|=(1870704577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_box_7 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (126719003/312500000 : ℝ)*x 0 + (4368662131/10000000000 : ℝ)*x 1 + (4368661691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126719003/312500000 : ℝ)^4565 ≤ (15617059659893/50000000000000 : ℝ)^3541 := by
    have hnat : (126719003 : ℕ)^4565*50000000000000^3541 ≤ 15617059659893^3541*312500000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126719003 312500000 15617059659893 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4368662131/10000000000 : ℝ)^4565 ≤ (6876588512269/20000000000000 : ℝ)^3541 := by
    have hnat : (4368662131 : ℕ)^4565*20000000000000^3541 ≤ 6876588512269^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368662131 10000000000 6876588512269 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4368661691/10000000000 : ℝ)^4565 ≤ (6876587619391/20000000000000 : ℝ)^3541 := by
    have hnat : (4368661691 : ℕ)^4565*20000000000000^3541 ≤ 6876587619391^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368661691 10000000000 6876587619391 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(126719003/312500000 : ℝ), (4368662131/10000000000 : ℝ), (4368661691/10000000000 : ℝ)] ![(15617059659893/50000000000000 : ℝ), (6876588512269/20000000000000 : ℝ), (6876587619391/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(126719003/312500000 : ℝ)|^4565 ≤ (15617059659893/50000000000000 : ℝ)^3541
        have hw : |(126719003/312500000 : ℝ)|=(126719003/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4368662131/10000000000 : ℝ)|^4565 ≤ (6876588512269/20000000000000 : ℝ)^3541
        have hw : |(4368662131/10000000000 : ℝ)|=(4368662131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4368661691/10000000000 : ℝ)|^4565 ≤ (6876587619391/20000000000000 : ℝ)^3541
        have hw : |(4368661691/10000000000 : ℝ)|=(4368661691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_box_8 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1961278997/10000000000 : ℝ)*x 0 + (513461121/1000000000 : ℝ)*x 1 + (5420844133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1961278997/10000000000 : ℝ)^4565 ≤ (6122421112769/50000000000000 : ℝ)^3541 := by
    have hnat : (1961278997 : ℕ)^4565*50000000000000^3541 ≤ 6122421112769^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961278997 10000000000 6122421112769 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513461121/1000000000 : ℝ)^4565 ≤ (8468783379971/20000000000000 : ℝ)^3541 := by
    have hnat : (513461121 : ℕ)^4565*20000000000000^3541 ≤ 8468783379971^3541*1000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513461121 1000000000 8468783379971 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420844133/10000000000 : ℝ)^4565 ≤ (9082248172073/20000000000000 : ℝ)^3541 := by
    have hnat : (5420844133 : ℕ)^4565*20000000000000^3541 ≤ 9082248172073^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420844133 10000000000 9082248172073 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1961278997/10000000000 : ℝ), (513461121/1000000000 : ℝ), (5420844133/10000000000 : ℝ)] ![(6122421112769/50000000000000 : ℝ), (8468783379971/20000000000000 : ℝ), (9082248172073/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1961278997/10000000000 : ℝ)|^4565 ≤ (6122421112769/50000000000000 : ℝ)^3541
        have hw : |(-1961278997/10000000000 : ℝ)|=(1961278997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513461121/1000000000 : ℝ)|^4565 ≤ (8468783379971/20000000000000 : ℝ)^3541
        have hw : |(513461121/1000000000 : ℝ)|=(513461121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420844133/10000000000 : ℝ)|^4565 ≤ (9082248172073/20000000000000 : ℝ)^3541
        have hw : |(5420844133/10000000000 : ℝ)|=(5420844133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_box_9 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628414761/5000000000 : ℝ)*x 0 + (-1797264691/10000000000 : ℝ)*x 1 + (1355210987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628414761/5000000000 : ℝ)^4565 ≤ (43647739269389/100000000000000 : ℝ)^3541 := by
    have hnat : (2628414761 : ℕ)^4565*100000000000000^3541 ≤ 43647739269389^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628414761 5000000000 43647739269389 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1797264691/10000000000 : ℝ)^4565 ≤ (109410218563/1000000000000 : ℝ)^3541 := by
    have hnat : (1797264691 : ℕ)^4565*1000000000000^3541 ≤ 109410218563^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797264691 10000000000 109410218563 1000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355210987/2500000000 : ℝ)^4565 ≤ (22705619431211/50000000000000 : ℝ)^3541 := by
    have hnat : (1355210987 : ℕ)^4565*50000000000000^3541 ≤ 22705619431211^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355210987 2500000000 22705619431211 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628414761/5000000000 : ℝ), (-1797264691/10000000000 : ℝ), (1355210987/2500000000 : ℝ)] ![(43647739269389/100000000000000 : ℝ), (109410218563/1000000000000 : ℝ), (22705619431211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628414761/5000000000 : ℝ)|^4565 ≤ (43647739269389/100000000000000 : ℝ)^3541
        have hw : |(2628414761/5000000000 : ℝ)|=(2628414761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1797264691/10000000000 : ℝ)|^4565 ≤ (109410218563/1000000000000 : ℝ)^3541
        have hw : |(-1797264691/10000000000 : ℝ)|=(1797264691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355210987/2500000000 : ℝ)|^4565 ≤ (22705619431211/50000000000000 : ℝ)^3541
        have hw : |(1355210987/2500000000 : ℝ)|=(1355210987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_box_10 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051365937/2000000000 : ℝ)*x 0 + (16940137/31250000 : ℝ)*x 1 + (-224658077/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051365937/2000000000 : ℝ)^4565 ≤ (5455967626771/12500000000000 : ℝ)^3541 := by
    have hnat : (1051365937 : ℕ)^4565*12500000000000^3541 ≤ 5455967626771^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051365937 2000000000 5455967626771 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16940137/31250000 : ℝ)^4565 ≤ (5676404712007/12500000000000 : ℝ)^3541 := by
    have hnat : (16940137 : ℕ)^4565*12500000000000^3541 ≤ 5676404712007^3541*31250000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16940137 31250000 5676404712007 12500000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224658077/1250000000 : ℝ)^4565 ≤ (10941021267697/100000000000000 : ℝ)^3541 := by
    have hnat : (224658077 : ℕ)^4565*100000000000000^3541 ≤ 10941021267697^3541*1250000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224658077 1250000000 10941021267697 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051365937/2000000000 : ℝ), (16940137/31250000 : ℝ), (-224658077/1250000000 : ℝ)] ![(5455967626771/12500000000000 : ℝ), (5676404712007/12500000000000 : ℝ), (10941021267697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051365937/2000000000 : ℝ)|^4565 ≤ (5455967626771/12500000000000 : ℝ)^3541
        have hw : |(1051365937/2000000000 : ℝ)|=(1051365937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16940137/31250000 : ℝ)|^4565 ≤ (5676404712007/12500000000000 : ℝ)^3541
        have hw : |(16940137/31250000 : ℝ)|=(16940137/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224658077/1250000000 : ℝ)|^4565 ≤ (10941021267697/100000000000000 : ℝ)^3541
        have hw : |(-224658077/1250000000 : ℝ)|=(224658077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_box_11 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2256838559/5000000000 : ℝ)*x 0 + (4138868673/10000000000 : ℝ)*x 1 + (4138868761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2256838559/5000000000 : ℝ)^4565 ≤ (35861321299433/100000000000000 : ℝ)^3541 := by
    have hnat : (2256838559 : ℕ)^4565*100000000000000^3541 ≤ 35861321299433^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256838559 5000000000 35861321299433 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4138868673/10000000000 : ℝ)^4565 ≤ (8017334726851/25000000000000 : ℝ)^3541 := by
    have hnat : (4138868673 : ℕ)^4565*25000000000000^3541 ≤ 8017334726851^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138868673 10000000000 8017334726851 25000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4138868761/10000000000 : ℝ)^4565 ≤ (16034669893219/50000000000000 : ℝ)^3541 := by
    have hnat : (4138868761 : ℕ)^4565*50000000000000^3541 ≤ 16034669893219^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138868761 10000000000 16034669893219 50000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2256838559/5000000000 : ℝ), (4138868673/10000000000 : ℝ), (4138868761/10000000000 : ℝ)] ![(35861321299433/100000000000000 : ℝ), (8017334726851/25000000000000 : ℝ), (16034669893219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2256838559/5000000000 : ℝ)|^4565 ≤ (35861321299433/100000000000000 : ℝ)^3541
        have hw : |(2256838559/5000000000 : ℝ)|=(2256838559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4138868673/10000000000 : ℝ)|^4565 ≤ (8017334726851/25000000000000 : ℝ)^3541
        have hw : |(4138868673/10000000000 : ℝ)|=(4138868673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4138868761/10000000000 : ℝ)|^4565 ≤ (16034669893219/50000000000000 : ℝ)^3541
        have hw : |(4138868761/10000000000 : ℝ)|=(4138868761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_box_12 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-343195377/2000000000 : ℝ)*x 0 + (2753331923/5000000000 : ℝ)*x 1 + (1307307379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343195377/2000000000 : ℝ)^4565 ≤ (1030729023937/10000000000000 : ℝ)^3541 := by
    have hnat : (343195377 : ℕ)^4565*10000000000000^3541 ≤ 1030729023937^3541*2000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343195377 2000000000 1030729023937 10000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2753331923/5000000000 : ℝ)^4565 ≤ (46340180878503/100000000000000 : ℝ)^3541 := by
    have hnat : (2753331923 : ℕ)^4565*100000000000000^3541 ≤ 46340180878503^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753331923 5000000000 46340180878503 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307307379/2500000000 : ℝ)^4565 ≤ (1354766527019/3125000000000 : ℝ)^3541 := by
    have hnat : (1307307379 : ℕ)^4565*3125000000000^3541 ≤ 1354766527019^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307307379 2500000000 1354766527019 3125000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-343195377/2000000000 : ℝ), (2753331923/5000000000 : ℝ), (1307307379/2500000000 : ℝ)] ![(1030729023937/10000000000000 : ℝ), (46340180878503/100000000000000 : ℝ), (1354766527019/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-343195377/2000000000 : ℝ)|^4565 ≤ (1030729023937/10000000000000 : ℝ)^3541
        have hw : |(-343195377/2000000000 : ℝ)|=(343195377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2753331923/5000000000 : ℝ)|^4565 ≤ (46340180878503/100000000000000 : ℝ)^3541
        have hw : |(2753331923/5000000000 : ℝ)|=(2753331923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307307379/2500000000 : ℝ)|^4565 ≤ (1354766527019/3125000000000 : ℝ)^3541
        have hw : |(1307307379/2500000000 : ℝ)|=(1307307379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_box_13 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347504173/2500000000 : ℝ)*x 0 + (-938382169/5000000000 : ℝ)*x 1 + (2614614571/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347504173/2500000000 : ℝ)^4565 ≤ (45078588168369/100000000000000 : ℝ)^3541 := by
    have hnat : (1347504173 : ℕ)^4565*100000000000000^3541 ≤ 45078588168369^3541*2500000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347504173 2500000000 45078588168369 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (938382169/5000000000 : ℝ)^4565 ≤ (11568886945303/100000000000000 : ℝ)^3541 := by
    have hnat : (938382169 : ℕ)^4565*100000000000000^3541 ≤ 11568886945303^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938382169 5000000000 11568886945303 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614614571/5000000000 : ℝ)^4565 ≤ (2167626243367/5000000000000 : ℝ)^3541 := by
    have hnat : (2614614571 : ℕ)^4565*5000000000000^3541 ≤ 2167626243367^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614614571 5000000000 2167626243367 5000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347504173/2500000000 : ℝ), (-938382169/5000000000 : ℝ), (2614614571/5000000000 : ℝ)] ![(45078588168369/100000000000000 : ℝ), (11568886945303/100000000000000 : ℝ), (2167626243367/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347504173/2500000000 : ℝ)|^4565 ≤ (45078588168369/100000000000000 : ℝ)^3541
        have hw : |(1347504173/2500000000 : ℝ)|=(1347504173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-938382169/5000000000 : ℝ)|^4565 ≤ (11568886945303/100000000000000 : ℝ)^3541
        have hw : |(-938382169/5000000000 : ℝ)|=(938382169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614614571/5000000000 : ℝ)|^4565 ≤ (2167626243367/5000000000000 : ℝ)^3541
        have hw : |(2614614571/5000000000 : ℝ)|=(2614614571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_box_14 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695008317/5000000000 : ℝ)*x 0 + (5229229239/10000000000 : ℝ)*x 1 + (-938382143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695008317/5000000000 : ℝ)^4565 ≤ (45078587543019/100000000000000 : ℝ)^3541 := by
    have hnat : (2695008317 : ℕ)^4565*100000000000000^3541 ≤ 45078587543019^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695008317 5000000000 45078587543019 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229229239/10000000000 : ℝ)^4565 ≤ (8670505180813/20000000000000 : ℝ)^3541 := by
    have hnat : (5229229239 : ℕ)^4565*20000000000000^3541 ≤ 8670505180813^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229229239 10000000000 8670505180813 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (938382143/5000000000 : ℝ)^4565 ≤ (2313777306413/20000000000000 : ℝ)^3541 := by
    have hnat : (938382143 : ℕ)^4565*20000000000000^3541 ≤ 2313777306413^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938382143 5000000000 2313777306413 20000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695008317/5000000000 : ℝ), (5229229239/10000000000 : ℝ), (-938382143/5000000000 : ℝ)] ![(45078587543019/100000000000000 : ℝ), (8670505180813/20000000000000 : ℝ), (2313777306413/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695008317/5000000000 : ℝ)|^4565 ≤ (45078587543019/100000000000000 : ℝ)^3541
        have hw : |(2695008317/5000000000 : ℝ)|=(2695008317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229229239/10000000000 : ℝ)|^4565 ≤ (8670505180813/20000000000000 : ℝ)^3541
        have hw : |(5229229239/10000000000 : ℝ)|=(5229229239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-938382143/5000000000 : ℝ)|^4565 ≤ (2313777306413/20000000000000 : ℝ)^3541
        have hw : |(-938382143/5000000000 : ℝ)|=(938382143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1534_box_15 (p : ℝ) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4014978753/10000000000 : ℝ)*x 0 + (2194104599/5000000000 : ℝ)*x 1 + (4388209429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4014978753/10000000000 : ℝ)^4565 ≤ (30837193760841/100000000000000 : ℝ)^3541 := by
    have hnat : (4014978753 : ℕ)^4565*100000000000000^3541 ≤ 30837193760841^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014978753 10000000000 30837193760841 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194104599/5000000000 : ℝ)^4565 ≤ (34581401938231/100000000000000 : ℝ)^3541 := by
    have hnat : (2194104599 : ℕ)^4565*100000000000000^3541 ≤ 34581401938231^3541*5000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194104599 5000000000 34581401938231 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4388209429/10000000000 : ℝ)^4565 ≤ (34581404285063/100000000000000 : ℝ)^3541 := by
    have hnat : (4388209429 : ℕ)^4565*100000000000000^3541 ≤ 34581404285063^3541*10000000000^4565 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4388209429 10000000000 34581404285063 100000000000000 4565 3541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4565/1024 : ℝ)) 4565 3541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4014978753/10000000000 : ℝ), (2194104599/5000000000 : ℝ), (4388209429/10000000000 : ℝ)] ![(30837193760841/100000000000000 : ℝ), (34581401938231/100000000000000 : ℝ), (34581404285063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4014978753/10000000000 : ℝ)|^4565 ≤ (30837193760841/100000000000000 : ℝ)^3541
        have hw : |(4014978753/10000000000 : ℝ)|=(4014978753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2194104599/5000000000 : ℝ)|^4565 ≤ (34581401938231/100000000000000 : ℝ)^3541
        have hw : |(2194104599/5000000000 : ℝ)|=(2194104599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4388209429/10000000000 : ℝ)|^4565 ≤ (34581404285063/100000000000000 : ℝ)^3541
        have hw : |(4388209429/10000000000 : ℝ)|=(4388209429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1534_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6377/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58731/100000 : ℝ) ∧ (10069/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43071/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5499/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5499/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5499/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5499/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5499/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5499/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5499/50000 : ℝ) ^ (4563/1024 : ℝ) ≤ (534615427874709/10000000000000000000 : ℝ) := by
    have hpowers : (5499/50000 : ℝ)^4563 ≤ (534615427874709/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5499 : ℕ)^4563*10000000000000000000^1024 ≤ 534615427874709^1024*50000^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5499 50000 534615427874709 10000000000000000000 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5499/50000 : ℝ)) (X := (534615427874709/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4563/1024 : ℝ) ≤ (24551332583407883/100000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4563 ≤ (24551332583407883/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4563*100000000000000000000^1024 ≤ 24551332583407883^1024*25000^4563 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 24551332583407883 100000000000000000000 4563 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (24551332583407883/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000534615427874709/5000000000000000000 : ℝ) ≤ (10000239940171051/10000000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (5000534615427874709/5000000000000000000 : ℝ)^1024 ≤ (10000239940171051/10000000000000000 : ℝ)^4563 := by
      have hnat : (5000534615427874709 : ℕ)^1024*10000000000000000^4563 ≤ 10000239940171051^4563*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000534615427874709 5000000000000000000 10000239940171051 10000000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000239940171051/10000000000000000 : ℝ)) (X := (5000534615427874709/5000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029897486862154973/100000000000000000000 : ℝ) ≤ (10000670862977351/10000000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (100029897486862154973/100000000000000000000 : ℝ)^1024 ≤ (10000670862977351/10000000000000000 : ℝ)^4563 := by
      have hnat : (100029897486862154973 : ℕ)^1024*10000000000000000^4563 ≤ 10000670862977351^4563*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029897486862154973 100000000000000000000 10000670862977351 10000000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000670862977351/10000000000000000 : ℝ)) (X := (100029897486862154973/100000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024551332583407883/50000000000000000000 : ℝ) ≤ (10001101785783651/10000000000000000 : ℝ) ^ (4563/1024 : ℝ) := by
    have hpowers : (50024551332583407883/50000000000000000000 : ℝ)^1024 ≤ (10001101785783651/10000000000000000 : ℝ)^4563 := by
      have hnat : (50024551332583407883 : ℕ)^1024*10000000000000000^4563 ≤ 10001101785783651^4563*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024551332583407883 50000000000000000000 10001101785783651 10000000000000000 1024 4563 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001101785783651/10000000000000000 : ℝ)) (X := (50024551332583407883/50000000000000000000 : ℝ)) (by norm_num) 4563 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(534615427874709/10000000000000000000 : ℝ) ≤ ((22425798896779979993/22430000000000000000 : ℝ)+2*(4309228063/4486000000000 : ℝ)*(5499/50000 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (22425798896779979993/22430000000000000000 : ℝ)+2*(4309228063/4486000000000 : ℝ)*(5499/50000 : ℝ)=(10000239940171051/10000000000000000 : ℝ) by norm_num, show 1+2*(534615427874709/10000000000000000000 : ℝ)=(5000534615427874709/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24551332583407883/100000000000000000000 : ℝ)+(534615427874709/10000000000000000000 : ℝ) ≤ ((22425798896779979993/22430000000000000000 : ℝ)+(4309228063/4486000000000 : ℝ)*((3871/25000 : ℝ)+(5499/50000 : ℝ)))^(4563/1024 : ℝ) := by
    rw [show (22425798896779979993/22430000000000000000 : ℝ)+(4309228063/4486000000000 : ℝ)*((3871/25000 : ℝ)+(5499/50000 : ℝ))=(10000670862977351/10000000000000000 : ℝ) by norm_num, show 1+(24551332583407883/100000000000000000000 : ℝ)+(534615427874709/10000000000000000000 : ℝ)=(100029897486862154973/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24551332583407883/100000000000000000000 : ℝ) ≤ ((22425798896779979993/22430000000000000000 : ℝ)+2*(4309228063/4486000000000 : ℝ)*(3871/25000 : ℝ))^(4563/1024 : ℝ) := by
    rw [show (22425798896779979993/22430000000000000000 : ℝ)+2*(4309228063/4486000000000 : ℝ)*(3871/25000 : ℝ)=(10001101785783651/10000000000000000 : ℝ) by norm_num, show 1+2*(24551332583407883/100000000000000000000 : ℝ)=(50024551332583407883/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22425798896779979993/22430000000000000000 : ℝ)*(X 1 0+X 2 0)+(4309228063/4486000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (5499/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (22425798896779979993/22430000000000000000 : ℝ)) (alpha := (4309228063/4486000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22425798896779979993/22430000000000000000 : ℝ)*(X 0 1+X 2 1)+(4309228063/4486000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (5499/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (22425798896779979993/22430000000000000000 : ℝ)) (alpha := (4309228063/4486000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22425798896779979993/22430000000000000000 : ℝ)*(X 0 2+X 1 2)+(4309228063/4486000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4563/1024 : ℝ)) (lo := (5499/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (22425798896779979993/22430000000000000000 : ℝ)) (alpha := (4309228063/4486000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1626225859/10000000000 : ℝ)*X 0 0+(5400458183/10000000000 : ℝ)*X 0 1+(1350114399/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5271003087/10000000000 : ℝ)*X 1 0+(-902978191/5000000000 : ℝ)*X 1 1+(2700229303/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271003607/10000000000 : ℝ)*X 2 0+(5400457941/10000000000 : ℝ)*X 2 1+(-1805956587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((892347809/2000000000 : ℝ)*X 0 0+(833085507/2000000000 : ℝ)*X 0 1+(833085683/2000000000 : ℝ)*X 0 2+(892347809/2000000000 : ℝ)*X 1 0+(833085507/2000000000 : ℝ)*X 1 1+(833085683/2000000000 : ℝ)*X 1 2+(892347809/2000000000 : ℝ)*X 2 0+(833085507/2000000000 : ℝ)*X 2 1+(833085683/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1025597959/5000000000 : ℝ)*X 0 0+(5244269797/10000000000 : ℝ)*X 0 1+(163883441/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((168111327/312500000 : ℝ)*X 1 0+(-1870704299/10000000000 : ℝ)*X 1 1+(5244269903/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((672445291/1250000000 : ℝ)*X 2 0+(5244269833/10000000000 : ℝ)*X 2 1+(-1870704577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((126719003/312500000 : ℝ)*X 0 0+(4368662131/10000000000 : ℝ)*X 0 1+(4368661691/10000000000 : ℝ)*X 0 2+(126719003/312500000 : ℝ)*X 1 0+(4368662131/10000000000 : ℝ)*X 1 1+(4368661691/10000000000 : ℝ)*X 1 2+(126719003/312500000 : ℝ)*X 2 0+(4368662131/10000000000 : ℝ)*X 2 1+(4368661691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1961278997/10000000000 : ℝ)*X 0 0+(513461121/1000000000 : ℝ)*X 0 1+(5420844133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628414761/5000000000 : ℝ)*X 1 0+(-1797264691/10000000000 : ℝ)*X 1 1+(1355210987/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1051365937/2000000000 : ℝ)*X 2 0+(16940137/31250000 : ℝ)*X 2 1+(-224658077/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2256838559/5000000000 : ℝ)*X 0 0+(4138868673/10000000000 : ℝ)*X 0 1+(4138868761/10000000000 : ℝ)*X 0 2+(2256838559/5000000000 : ℝ)*X 1 0+(4138868673/10000000000 : ℝ)*X 1 1+(4138868761/10000000000 : ℝ)*X 1 2+(2256838559/5000000000 : ℝ)*X 2 0+(4138868673/10000000000 : ℝ)*X 2 1+(4138868761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-343195377/2000000000 : ℝ)*X 0 0+(2753331923/5000000000 : ℝ)*X 0 1+(1307307379/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1347504173/2500000000 : ℝ)*X 1 0+(-938382169/5000000000 : ℝ)*X 1 1+(2614614571/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2695008317/5000000000 : ℝ)*X 2 0+(5229229239/10000000000 : ℝ)*X 2 1+(-938382143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4014978753/10000000000 : ℝ)*X 0 0+(2194104599/5000000000 : ℝ)*X 0 1+(4388209429/10000000000 : ℝ)*X 0 2+(4014978753/10000000000 : ℝ)*X 1 0+(2194104599/5000000000 : ℝ)*X 1 1+(4388209429/10000000000 : ℝ)*X 1 2+(4014978753/10000000000 : ℝ)*X 2 0+(2194104599/5000000000 : ℝ)*X 2 1+(4388209429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1534_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6377/10000 : ℝ) ≤ (-143030627245573445720823441/224300000000000000000000000 : ℝ) := by norm_num
    linear_combination (867111/1000000000000 : ℝ)*(lower0) + (2581677/10000000000000 : ℝ)*(upper1) + (102769641/100000000000000 : ℝ)*(lower4) + (1127853056100877/50000000000000 : ℝ)*(major0) + (1127853056100877/50000000000000 : ℝ)*(major1) + (1127853056100877/50000000000000 : ℝ)*(major2) + (601923477/25000000000000 : ℝ)*(sp1) + (7907237163/100000000000000 : ℝ)*(sp2) + (93662557/10000000000000 : ℝ)*(sp3) + (197920202005869/6250000000000 : ℝ)*(sp4) + (158336133048971/5000000000000 : ℝ)*(sp5) + (1583358580718083/50000000000000 : ℝ)*(sp6) + (273188414195287/20000000000000 : ℝ)*(sp7) + (1836579423/100000000000000 : ℝ)*(sp12) + (682971503801003/50000000000000 : ℝ)*(f.failure) + (197920316792083/6250000000000 : ℝ)*(f.sum) + (6186139903551/2243000000000000000000000000 : ℝ)*base65 + (6785649887263253861/1121500000000000000000000000000000 : ℝ)*base67 + (6145880825308253861/1121500000000000000000000000000000 : ℝ)*base69 + (3315220616344246139/1121500000000000000000000000000000 : ℝ)*base72 + (12854302009237/2243000000000000000000000000 : ℝ)*base74 + (1966810711280253861/1121500000000000000000000000000000 : ℝ)*base75 + (7397723435673746139/1121500000000000000000000000000000 : ℝ)*base78 + (8742620400509246139/1121500000000000000000000000000000 : ℝ)*base80 + (2685546363431/560750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (48726327/5000000000000000000000 : ℝ)*base89 + (48726327/5000000000000000000000 : ℝ)*base91 + (48726327/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58731/100000 : ℝ) ≤ (3293506174309694792950379935827/5607500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37319707/20000000000000 : ℝ)*(upper0) + (6066831/12500000000000 : ℝ)*(upper2) + (88578831/100000000000000 : ℝ)*(upper3) + (110129623/100000000000000 : ℝ)*(upper4) + (4719129/20000000000000 : ℝ)*(upper5) + (23334559276587/1000000000000 : ℝ)*(major0) + (23334559276587/1000000000000 : ℝ)*(major1) + (23334559276587/1000000000000 : ℝ)*(major2) + (808577364538339/25000000000000 : ℝ)*(sp0) + (1617147107321089/50000000000000 : ℝ)*(sp1) + (808576008279461/25000000000000 : ℝ)*(sp2) + (282604882851669/20000000000000 : ℝ)*(sp3) + (7621755589/50000000000000 : ℝ)*(sp5) + (5425035513/100000000000000 : ℝ)*(sp6) + (282604882851669/20000000000000 : ℝ)*(f.failure) + (808577364538339/25000000000000 : ℝ)*(f.sum) + (5773600157203/2243000000000000000000000000 : ℝ)*base66 + (166971871471433891/22430000000000000000000000000000 : ℝ)*base67 + (200084750495393891/22430000000000000000000000000000 : ℝ)*base69 + (141869003213033891/22430000000000000000000000000000 : ℝ)*base71 + (20170849695249/2243000000000000000000000000 : ℝ)*base73 + (140038128130213891/22430000000000000000000000000000 : ℝ)*base75 + (158813927997386109/22430000000000000000000000000000 : ℝ)*base78 + (527667212455883891/22430000000000000000000000000000 : ℝ)*base79 + (4235348447361/1121500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2177079/2000000000000000000000 : ℝ)*base90 + (2177079/2000000000000000000000 : ℝ)*base92 + (2177079/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (10069/12500 : ℝ) ≤ (112927909391344015606618753700853/140187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6772903/50000000000000 : ℝ)*(upper0) + (7578129/20000000000000 : ℝ)*(lower3) + (7547331/20000000000000 : ℝ)*(upper4) + (631165504475993/25000000000000 : ℝ)*(major0) + (631165504475993/25000000000000 : ℝ)*(major1) + (631165504475993/25000000000000 : ℝ)*(major2) + (3388359423/25000000000000 : ℝ)*(sp1) + (2860425417/100000000000000 : ℝ)*(sp3) + (2298756251/100000000000000 : ℝ)*(sp4) + (3493660105642951/100000000000000 : ℝ)*(sp8) + (3493649570176253/100000000000000 : ℝ)*(sp9) + (1746831561806973/50000000000000 : ℝ)*(sp10) + (764403208153111/50000000000000 : ℝ)*(sp11) + (719214743/100000000000000 : ℝ)*(sp12) + (764404638365819/50000000000000 : ℝ)*(f.failure) + (1746831561806973/50000000000000 : ℝ)*(f.sum) + (14833428570997/2243000000000000000000000000 : ℝ)*base65 + (1441642023746808049/560750000000000000000000000000000 : ℝ)*base67 + (2421114061498808049/560750000000000000000000000000000 : ℝ)*base69 + (4045104799500558049/560750000000000000000000000000000 : ℝ)*base71 + (1004821543901/1121500000000000000000000000 : ℝ)*base74 + (1544682439809058049/560750000000000000000000000000000 : ℝ)*base75 + (3976362682954441951/560750000000000000000000000000000 : ℝ)*base78 + (3304689428468058049/560750000000000000000000000000000 : ℝ)*base79 + (5415330816937/2243000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (34284729/5000000000000000000000 : ℝ)*base90 + (34284729/5000000000000000000000 : ℝ)*base92 + (34284729/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-43071/50000 : ℝ) ≤ (-120756871445193938706460528883301/140187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5525799/25000000000000 : ℝ)*(lower3) + (17904883/100000000000000 : ℝ)*(lower4) + (15383389/50000000000000 : ℝ)*(upper5) + (641067514742181/25000000000000 : ℝ)*(major0) + (641067514742181/25000000000000 : ℝ)*(major1) + (641067514742181/25000000000000 : ℝ)*(major2) + (1788793779/50000000000000 : ℝ)*(sp4) + (78509650457/100000000000000 : ℝ)*(sp5) + (37819247211/50000000000000 : ℝ)*(sp6) + (4856996939/100000000000000 : ℝ)*(sp7) + (3604455792247981/100000000000000 : ℝ)*(sp12) + (1802190430092541/50000000000000 : ℝ)*(sp13) + (901095932835279/25000000000000 : ℝ)*(sp14) + (1552789072010347/100000000000000 : ℝ)*(sp15) + (776396964503643/50000000000000 : ℝ)*(f.failure) + (3604459369835539/100000000000000 : ℝ)*(f.sum) + (2653081939331/1121500000000000000000000000 : ℝ)*base65 + (1132879785797065267/560750000000000000000000000000000 : ℝ)*base68 + (3376233079044815267/560750000000000000000000000000000 : ℝ)*base70 + (83851598042065267/560750000000000000000000000000000 : ℝ)*base72 + (921623198403/560750000000000000000000000 : ℝ)*base73 + (731893999142065267/560750000000000000000000000000000 : ℝ)*base76 + (740166389498065267/560750000000000000000000000000000 : ℝ)*base78 + (1826825108124434733/560750000000000000000000000000000 : ℝ)*base79 + (8714111258543/1121500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (32274087/5000000000000000000000 : ℝ)*base89 + (32274087/5000000000000000000000 : ℝ)*base91 + (32274087/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1534_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6377/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58731/100000 : ℝ) else (10069/12500 : ℝ) ≤ X j i ∧ X j i ≤ (43071/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1534_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1534_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6377/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58731/100000 : ℝ) else (10069/12500 : ℝ) ≤ X j i ∧ X j i ≤ (43071/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1534_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1534_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4563/1024 : ℝ) ≤ p) (hpb : p ≤ (4565/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165139109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6377/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58731/100000 : ℝ) else (10069/12500 : ℝ) ≤ X j i ∧ X j i ≤ (43071/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1534_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

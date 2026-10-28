-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1111_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:05:00.86065+00:00
-- url     : https://prove2.me/submissions/2ae35a7d-c666-4987-94ba-c8581facf4af

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
theorem support_rectangle_w1111_s0_0 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1901661077/10000000000 : ℝ)*x 0 + (303076143/500000000 : ℝ)*x 1 + (4776539187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1901661077/10000000000 : ℝ)^519 ≤ (2761124653649/25000000000000 : ℝ)^391 := by
    have hnat : (1901661077 : ℕ)^519*25000000000000^391 ≤ 2761124653649^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901661077 10000000000 2761124653649 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (303076143/500000000 : ℝ)^519 ≤ (51452497783353/100000000000000 : ℝ)^391 := by
    have hnat : (303076143 : ℕ)^519*100000000000000^391 ≤ 51452497783353^391*500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303076143 500000000 51452497783353 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4776539187/10000000000 : ℝ)^519 ≤ (37503003582993/100000000000000 : ℝ)^391 := by
    have hnat : (4776539187 : ℕ)^519*100000000000000^391 ≤ 37503003582993^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4776539187 10000000000 37503003582993 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1901661077/10000000000 : ℝ), (303076143/500000000 : ℝ), (4776539187/10000000000 : ℝ)] ![(2761124653649/25000000000000 : ℝ), (51452497783353/100000000000000 : ℝ), (37503003582993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1901661077/10000000000 : ℝ)|^519 ≤ (2761124653649/25000000000000 : ℝ)^391
        have hw : |(-1901661077/10000000000 : ℝ)|=(1901661077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(303076143/500000000 : ℝ)|^519 ≤ (51452497783353/100000000000000 : ℝ)^391
        have hw : |(303076143/500000000 : ℝ)|=(303076143/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4776539187/10000000000 : ℝ)|^519 ≤ (37503003582993/100000000000000 : ℝ)^391
        have hw : |(4776539187/10000000000 : ℝ)|=(4776539187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s0_1 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5518539627/10000000000 : ℝ)*x 0 + (-659996931/2500000000 : ℝ)*x 1 + (1194134819/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518539627/10000000000 : ℝ)^519 ≤ (45426182899557/100000000000000 : ℝ)^391 := by
    have hnat : (5518539627 : ℕ)^519*100000000000000^391 ≤ 45426182899557^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518539627 10000000000 45426182899557 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659996931/2500000000 : ℝ)^519 ≤ (8535406289109/50000000000000 : ℝ)^391 := by
    have hnat : (659996931 : ℕ)^519*50000000000000^391 ≤ 8535406289109^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659996931 2500000000 8535406289109 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194134819/2500000000 : ℝ)^519 ≤ (18751502255267/50000000000000 : ℝ)^391 := by
    have hnat : (1194134819 : ℕ)^519*50000000000000^391 ≤ 18751502255267^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194134819 2500000000 18751502255267 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518539627/10000000000 : ℝ), (-659996931/2500000000 : ℝ), (1194134819/2500000000 : ℝ)] ![(45426182899557/100000000000000 : ℝ), (8535406289109/50000000000000 : ℝ), (18751502255267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518539627/10000000000 : ℝ)|^519 ≤ (45426182899557/100000000000000 : ℝ)^391
        have hw : |(5518539627/10000000000 : ℝ)|=(5518539627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-659996931/2500000000 : ℝ)|^519 ≤ (8535406289109/50000000000000 : ℝ)^391
        have hw : |(-659996931/2500000000 : ℝ)|=(659996931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1194134819/2500000000 : ℝ)|^519 ≤ (18751502255267/50000000000000 : ℝ)^391
        have hw : |(1194134819/2500000000 : ℝ)|=(1194134819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s0_2 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5518539839/10000000000 : ℝ)*x 0 + (597067383/1250000000 : ℝ)*x 1 + (-2639987711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518539839/10000000000 : ℝ)^519 ≤ (4542618521593/10000000000000 : ℝ)^391 := by
    have hnat : (5518539839 : ℕ)^519*10000000000000^391 ≤ 4542618521593^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518539839 10000000000 4542618521593 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597067383/1250000000 : ℝ)^519 ≤ (3750300230111/10000000000000 : ℝ)^391 := by
    have hnat : (597067383 : ℕ)^519*10000000000000^391 ≤ 3750300230111^391*1250000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597067383 1250000000 3750300230111 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2639987711/10000000000 : ℝ)^519 ≤ (8535406233319/50000000000000 : ℝ)^391 := by
    have hnat : (2639987711 : ℕ)^519*50000000000000^391 ≤ 8535406233319^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639987711 10000000000 8535406233319 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518539839/10000000000 : ℝ), (597067383/1250000000 : ℝ), (-2639987711/10000000000 : ℝ)] ![(4542618521593/10000000000000 : ℝ), (3750300230111/10000000000000 : ℝ), (8535406233319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518539839/10000000000 : ℝ)|^519 ≤ (4542618521593/10000000000000 : ℝ)^391
        have hw : |(5518539839/10000000000 : ℝ)|=(5518539839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597067383/1250000000 : ℝ)|^519 ≤ (3750300230111/10000000000000 : ℝ)^391
        have hw : |(597067383/1250000000 : ℝ)|=(597067383/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2639987711/10000000000 : ℝ)|^519 ≤ (8535406233319/50000000000000 : ℝ)^391
        have hw : |(-2639987711/10000000000 : ℝ)|=(2639987711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s0_3 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4203509913/10000000000 : ℝ)*x 0 + (390319811/1250000000 : ℝ)*x 1 + (5530728/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203509913/10000000000 : ℝ)^519 ≤ (31651592724553/100000000000000 : ℝ)^391 := by
    have hnat : (4203509913 : ℕ)^519*100000000000000^391 ≤ 31651592724553^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203509913 10000000000 31651592724553 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (390319811/1250000000 : ℝ)^519 ≤ (5332988886313/25000000000000 : ℝ)^391 := by
    have hnat : (390319811 : ℕ)^519*25000000000000^391 ≤ 5332988886313^391*1250000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390319811 1250000000 5332988886313 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5530728/9765625 : ℝ)^519 ≤ (47016451715003/100000000000000 : ℝ)^391 := by
    have hnat : (5530728 : ℕ)^519*100000000000000^391 ≤ 47016451715003^391*9765625^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5530728 9765625 47016451715003 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203509913/10000000000 : ℝ), (390319811/1250000000 : ℝ), (5530728/9765625 : ℝ)] ![(31651592724553/100000000000000 : ℝ), (5332988886313/25000000000000 : ℝ), (47016451715003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203509913/10000000000 : ℝ)|^519 ≤ (31651592724553/100000000000000 : ℝ)^391
        have hw : |(4203509913/10000000000 : ℝ)|=(4203509913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(390319811/1250000000 : ℝ)|^519 ≤ (5332988886313/25000000000000 : ℝ)^391
        have hw : |(390319811/1250000000 : ℝ)|=(390319811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5530728/9765625 : ℝ)|^519 ≤ (47016451715003/100000000000000 : ℝ)^391
        have hw : |(5530728/9765625 : ℝ)|=(5530728/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s0_4 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-953449809/5000000000 : ℝ)*x 0 + (2404851431/5000000000 : ℝ)*x 1 + (376699681/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (953449809/5000000000 : ℝ)^519 ≤ (11084901231347/100000000000000 : ℝ)^391 := by
    have hnat : (953449809 : ℕ)^519*100000000000000^391 ≤ 11084901231347^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953449809 5000000000 11084901231347 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2404851431/5000000000 : ℝ)^519 ≤ (37849021405041/100000000000000 : ℝ)^391 := by
    have hnat : (2404851431 : ℕ)^519*100000000000000^391 ≤ 37849021405041^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2404851431 5000000000 37849021405041 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (376699681/625000000 : ℝ)^519 ≤ (51066077352249/100000000000000 : ℝ)^391 := by
    have hnat : (376699681 : ℕ)^519*100000000000000^391 ≤ 51066077352249^391*625000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376699681 625000000 51066077352249 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-953449809/5000000000 : ℝ), (2404851431/5000000000 : ℝ), (376699681/625000000 : ℝ)] ![(11084901231347/100000000000000 : ℝ), (37849021405041/100000000000000 : ℝ), (51066077352249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-953449809/5000000000 : ℝ)|^519 ≤ (11084901231347/100000000000000 : ℝ)^391
        have hw : |(-953449809/5000000000 : ℝ)|=(953449809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2404851431/5000000000 : ℝ)|^519 ≤ (37849021405041/100000000000000 : ℝ)^391
        have hw : |(2404851431/5000000000 : ℝ)|=(2404851431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(376699681/625000000 : ℝ)|^519 ≤ (51066077352249/100000000000000 : ℝ)^391
        have hw : |(376699681/625000000 : ℝ)|=(376699681/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s0_5 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2584767513/5000000000 : ℝ)*x 0 + (-1389332917/10000000000 : ℝ)*x 1 + (3013598539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584767513/5000000000 : ℝ)^519 ≤ (20826453555773/50000000000000 : ℝ)^391 := by
    have hnat : (2584767513 : ℕ)^519*50000000000000^391 ≤ 20826453555773^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584767513 5000000000 20826453555773 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1389332917/10000000000 : ℝ)^519 ≤ (3640495492643/50000000000000 : ℝ)^391 := by
    have hnat : (1389332917 : ℕ)^519*50000000000000^391 ≤ 3640495492643^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389332917 10000000000 3640495492643 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3013598539/5000000000 : ℝ)^519 ≤ (6383262736447/12500000000000 : ℝ)^391 := by
    have hnat : (3013598539 : ℕ)^519*12500000000000^391 ≤ 6383262736447^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3013598539 5000000000 6383262736447 12500000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584767513/5000000000 : ℝ), (-1389332917/10000000000 : ℝ), (3013598539/5000000000 : ℝ)] ![(20826453555773/50000000000000 : ℝ), (3640495492643/50000000000000 : ℝ), (6383262736447/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584767513/5000000000 : ℝ)|^519 ≤ (20826453555773/50000000000000 : ℝ)^391
        have hw : |(2584767513/5000000000 : ℝ)|=(2584767513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1389332917/10000000000 : ℝ)|^519 ≤ (3640495492643/50000000000000 : ℝ)^391
        have hw : |(-1389332917/10000000000 : ℝ)|=(1389332917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3013598539/5000000000 : ℝ)|^519 ≤ (6383262736447/12500000000000 : ℝ)^391
        have hw : |(3013598539/5000000000 : ℝ)|=(3013598539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s0_6 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5169537889/10000000000 : ℝ)*x 0 + (6027195401/10000000000 : ℝ)*x 1 + (-694665613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5169537889/10000000000 : ℝ)^519 ≤ (41652937731591/100000000000000 : ℝ)^391 := by
    have hnat : (5169537889 : ℕ)^519*100000000000000^391 ≤ 41652937731591^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169537889 10000000000 41652937731591 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6027195401/10000000000 : ℝ)^519 ≤ (51066083031607/100000000000000 : ℝ)^391 := by
    have hnat : (6027195401 : ℕ)^519*100000000000000^391 ≤ 51066083031607^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6027195401 10000000000 51066083031607 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (694665613/5000000000 : ℝ)^519 ≤ (7280979222281/100000000000000 : ℝ)^391 := by
    have hnat : (694665613 : ℕ)^519*100000000000000^391 ≤ 7280979222281^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694665613 5000000000 7280979222281 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5169537889/10000000000 : ℝ), (6027195401/10000000000 : ℝ), (-694665613/5000000000 : ℝ)] ![(41652937731591/100000000000000 : ℝ), (51066083031607/100000000000000 : ℝ), (7280979222281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5169537889/10000000000 : ℝ)|^519 ≤ (41652937731591/100000000000000 : ℝ)^391
        have hw : |(5169537889/10000000000 : ℝ)|=(5169537889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6027195401/10000000000 : ℝ)|^519 ≤ (51066083031607/100000000000000 : ℝ)^391
        have hw : |(6027195401/10000000000 : ℝ)|=(6027195401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-694665613/5000000000 : ℝ)|^519 ≤ (7280979222281/100000000000000 : ℝ)^391
        have hw : |(-694665613/5000000000 : ℝ)|=(694665613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s0_7 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1053466283/2500000000 : ℝ)*x 0 + (2798945301/5000000000 : ℝ)*x 1 + (398804383/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053466283/2500000000 : ℝ)^519 ≤ (15877566387133/50000000000000 : ℝ)^391 := by
    have hnat : (1053466283 : ℕ)^519*50000000000000^391 ≤ 15877566387133^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053466283 2500000000 15877566387133 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2798945301/5000000000 : ℝ)^519 ≤ (23147614315671/50000000000000 : ℝ)^391 := by
    have hnat : (2798945301 : ℕ)^519*50000000000000^391 ≤ 23147614315671^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2798945301 5000000000 23147614315671 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398804383/1250000000 : ℝ)^519 ≤ (10974819293919/50000000000000 : ℝ)^391 := by
    have hnat : (398804383 : ℕ)^519*50000000000000^391 ≤ 10974819293919^391*1250000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398804383 1250000000 10974819293919 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053466283/2500000000 : ℝ), (2798945301/5000000000 : ℝ), (398804383/1250000000 : ℝ)] ![(15877566387133/50000000000000 : ℝ), (23147614315671/50000000000000 : ℝ), (10974819293919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053466283/2500000000 : ℝ)|^519 ≤ (15877566387133/50000000000000 : ℝ)^391
        have hw : |(1053466283/2500000000 : ℝ)|=(1053466283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2798945301/5000000000 : ℝ)|^519 ≤ (23147614315671/50000000000000 : ℝ)^391
        have hw : |(2798945301/5000000000 : ℝ)|=(2798945301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(398804383/1250000000 : ℝ)|^519 ≤ (10974819293919/50000000000000 : ℝ)^391
        have hw : |(398804383/1250000000 : ℝ)|=(398804383/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1111_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (57/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13967/50000 : ℝ)*pair X 0 0 := by
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
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8303/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8303 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8303*1^2048 ≤ 0^2048*1^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8303/2048 : ℝ) ≤ (2435969956579188649/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8303 ≤ (2435969956579188649/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8303*100000000000000000000^2048 ≤ 2435969956579188649^2048*5^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2435969956579188649 100000000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2435969956579188649/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8303 := by
      have hnat : (1 : ℕ)^2048*1^8303 ≤ 1^8303*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102435969956579188649/100000000000000000000 : ℝ) ≤ (2514885377673037/2500000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (102435969956579188649/100000000000000000000 : ℝ)^2048 ≤ (2514885377673037/2500000000000000 : ℝ)^8303 := by
      have hnat : (102435969956579188649 : ℕ)^2048*2500000000000000^8303 ≤ 2514885377673037^8303*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102435969956579188649 100000000000000000000 2514885377673037 2500000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514885377673037/2500000000000000 : ℝ)) (X := (102435969956579188649/100000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52435969956579188649/50000000000000000000 : ℝ) ≤ (1264885377673037/1250000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (52435969956579188649/50000000000000000000 : ℝ)^2048 ≤ (1264885377673037/1250000000000000 : ℝ)^8303 := by
      have hnat : (52435969956579188649 : ℕ)^2048*1250000000000000^8303 ≤ 1264885377673037^8303*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52435969956579188649 50000000000000000000 1264885377673037 1250000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1264885377673037/1250000000000000 : ℝ)) (X := (52435969956579188649/50000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14885377673037/1000000000000000 : ℝ)*(0 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(14885377673037/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2435969956579188649/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14885377673037/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8303/2048 : ℝ) := by
    rw [show (1 : ℝ)+(14885377673037/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2514885377673037/2500000000000000 : ℝ) by norm_num, show 1+(2435969956579188649/100000000000000000000 : ℝ)+(0 : ℝ)=(102435969956579188649/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2435969956579188649/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14885377673037/1000000000000000 : ℝ)*(2/5 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(14885377673037/1000000000000000 : ℝ)*(2/5 : ℝ)=(1264885377673037/1250000000000000 : ℝ) by norm_num, show 1+2*(2435969956579188649/100000000000000000000 : ℝ)=(52435969956579188649/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14885377673037/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14885377673037/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14885377673037/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14885377673037/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14885377673037/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14885377673037/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1901661077/10000000000 : ℝ)*X 0 0+(303076143/500000000 : ℝ)*X 0 1+(4776539187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5518539627/10000000000 : ℝ)*X 1 0+(-659996931/2500000000 : ℝ)*X 1 1+(1194134819/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5518539839/10000000000 : ℝ)*X 2 0+(597067383/1250000000 : ℝ)*X 2 1+(-2639987711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4203509913/10000000000 : ℝ)*X 0 0+(390319811/1250000000 : ℝ)*X 0 1+(5530728/9765625 : ℝ)*X 0 2+(4203509913/10000000000 : ℝ)*X 1 0+(390319811/1250000000 : ℝ)*X 1 1+(5530728/9765625 : ℝ)*X 1 2+(4203509913/10000000000 : ℝ)*X 2 0+(390319811/1250000000 : ℝ)*X 2 1+(5530728/9765625 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-953449809/5000000000 : ℝ)*X 0 0+(2404851431/5000000000 : ℝ)*X 0 1+(376699681/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2584767513/5000000000 : ℝ)*X 1 0+(-1389332917/10000000000 : ℝ)*X 1 1+(3013598539/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5169537889/10000000000 : ℝ)*X 2 0+(6027195401/10000000000 : ℝ)*X 2 1+(-694665613/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1053466283/2500000000 : ℝ)*X 0 0+(2798945301/5000000000 : ℝ)*X 0 1+(398804383/1250000000 : ℝ)*X 0 2+(1053466283/2500000000 : ℝ)*X 1 0+(2798945301/5000000000 : ℝ)*X 1 1+(398804383/1250000000 : ℝ)*X 1 2+(1053466283/2500000000 : ℝ)*X 2 0+(2798945301/5000000000 : ℝ)*X 2 1+(398804383/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (142900054800849890745921/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3857417/6250000000000 : ℝ)*(base1) + (1416338941/100000000000000 : ℝ)*(base19) + (671518053/50000000000000 : ℝ)*(base23) + (51599573/50000000000000 : ℝ)*(base24) + (10332093/3125000000000 : ℝ)*(upper3) + (292948054528711/50000000000000 : ℝ)*(major0) + (292948054528711/50000000000000 : ℝ)*(major1) + (292948054528711/50000000000000 : ℝ)*(major2) + (24319521774997/3125000000000 : ℝ)*(sp0) + (194556577556487/25000000000000 : ℝ)*(sp1) + (389113140164819/50000000000000 : ℝ)*(sp2) + (196780857857213/50000000000000 : ℝ)*(sp3) + (3091483657/100000000000000 : ℝ)*(sp4) + (630895861/25000000000000 : ℝ)*(sp7) + (393564301016543/100000000000000 : ℝ)*(f.failure) + (778227726564889/100000000000000 : ℝ)*(f.sum) + (14047389265307/25000000000000000000000000000 : ℝ)*base65 + (87251239565307/50000000000000000000000000000 : ℝ)*base67 + (280786723334693/50000000000000000000000000000 : ℝ)*base70 + (164356160034693/50000000000000000000000000000 : ℝ)*base72 + (49472916465307/25000000000000000000000000000 : ℝ)*base73 + (159020769734693/50000000000000000000000000000 : ℝ)*base76 + (164046504334693/50000000000000000000000000000 : ℝ)*base78 + (455901113334693/50000000000000000000000000000 : ℝ)*base80 + (19207634684693/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (64523003/10000000000000000000000 : ℝ)*base89 + (64523003/10000000000000000000000 : ℝ)*base91 + (64523003/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46668415629549069247653/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70165361/25000000000000 : ℝ)*(base13) + (61974869/10000000000000 : ℝ)*(base23) + (191332169/100000000000000 : ℝ)*(base39) + (33859539/50000000000000 : ℝ)*(upper3) + (7126119/20000000000000 : ℝ)*(upper4) + (43833069/25000000000000 : ℝ)*(upper5) + (309183736327123/50000000000000 : ℝ)*(major0) + (309183736327123/50000000000000 : ℝ)*(major1) + (154591820330519/25000000000000 : ℝ)*(major2) + (710462621/100000000000000 : ℝ)*(sp2) + (205339525988191/25000000000000 : ℝ)*(sp4) + (12833724759597/1562500000000 : ℝ)*(sp5) + (410678622867533/50000000000000 : ℝ)*(sp6) + (83075261427511/20000000000000 : ℝ)*(sp7) + (83075261427511/20000000000000 : ℝ)*(f.failure) + (821358575946377/100000000000000 : ℝ)*(f.sum) + (263701727485043/50000000000000000000000000000 : ℝ)*base66 + (175416237566203/25000000000000000000000000000 : ℝ)*base67 + (161929284317449/50000000000000000000000000000 : ℝ)*base70 + (32486587183797/25000000000000000000000000000 : ℝ)*base72 + (68554009214957/50000000000000000000000000000 : ℝ)*base73 + (62378868317449/50000000000000000000000000000 : ℝ)*base76 + (355826471232551/50000000000000000000000000000 : ℝ)*base77 + (313840952882551/50000000000000000000000000000 : ℝ)*base79 + (31008407942449/25000000000000000000000000000 : ℝ)*base82 + (9461069/2000000000000000000000 : ℝ)*base90 + (9461069/2000000000000000000000 : ℝ)*base92 + (10538931/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1111_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (57/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13967/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1111_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1111_s1_0 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1054283637/5000000000 : ℝ)*x 0 + (2854934163/5000000000 : ℝ)*x 1 + (2497859103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054283637/5000000000 : ℝ)^519 ≤ (2533460398831/20000000000000 : ℝ)^391 := by
    have hnat : (1054283637 : ℕ)^519*20000000000000^391 ≤ 2533460398831^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054283637 5000000000 2533460398831 20000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2854934163/5000000000 : ℝ)^519 ≤ (371316157127/781250000000 : ℝ)^391 := by
    have hnat : (2854934163 : ℕ)^519*781250000000^391 ≤ 371316157127^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2854934163 5000000000 371316157127 781250000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2497859103/5000000000 : ℝ)^519 ≤ (1990211494161/5000000000000 : ℝ)^391 := by
    have hnat : (2497859103 : ℕ)^519*5000000000000^391 ≤ 1990211494161^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2497859103 5000000000 1990211494161 5000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1054283637/5000000000 : ℝ), (2854934163/5000000000 : ℝ), (2497859103/5000000000 : ℝ)] ![(2533460398831/20000000000000 : ℝ), (371316157127/781250000000 : ℝ), (1990211494161/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1054283637/5000000000 : ℝ)|^519 ≤ (2533460398831/20000000000000 : ℝ)^391
        have hw : |(-1054283637/5000000000 : ℝ)|=(1054283637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2854934163/5000000000 : ℝ)|^519 ≤ (371316157127/781250000000 : ℝ)^391
        have hw : |(2854934163/5000000000 : ℝ)|=(2854934163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2497859103/5000000000 : ℝ)|^519 ≤ (1990211494161/5000000000000 : ℝ)^391
        have hw : |(2497859103/5000000000 : ℝ)|=(2497859103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s1_1 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (677603217/1250000000 : ℝ)*x 0 + (-1247288217/5000000000 : ℝ)*x 1 + (4995718163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677603217/1250000000 : ℝ)^519 ≤ (22180819692533/50000000000000 : ℝ)^391 := by
    have hnat : (677603217 : ℕ)^519*50000000000000^391 ≤ 22180819692533^391*1250000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677603217 1250000000 22180819692533 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1247288217/5000000000 : ℝ)^519 ≤ (1979266395733/12500000000000 : ℝ)^391 := by
    have hnat : (1247288217 : ℕ)^519*12500000000000^391 ≤ 1979266395733^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1247288217 5000000000 1979266395733 12500000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4995718163/10000000000 : ℝ)^519 ≤ (39804229428451/100000000000000 : ℝ)^391 := by
    have hnat : (4995718163 : ℕ)^519*100000000000000^391 ≤ 39804229428451^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4995718163 10000000000 39804229428451 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677603217/1250000000 : ℝ), (-1247288217/5000000000 : ℝ), (4995718163/10000000000 : ℝ)] ![(22180819692533/50000000000000 : ℝ), (1979266395733/12500000000000 : ℝ), (39804229428451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677603217/1250000000 : ℝ)|^519 ≤ (22180819692533/50000000000000 : ℝ)^391
        have hw : |(677603217/1250000000 : ℝ)|=(677603217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1247288217/5000000000 : ℝ)|^519 ≤ (1979266395733/12500000000000 : ℝ)^391
        have hw : |(-1247288217/5000000000 : ℝ)|=(1247288217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4995718163/10000000000 : ℝ)|^519 ≤ (39804229428451/100000000000000 : ℝ)^391
        have hw : |(4995718163/10000000000 : ℝ)|=(4995718163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s1_2 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5420827043/10000000000 : ℝ)*x 0 + (78058077/156250000 : ℝ)*x 1 + (-24945763/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420827043/10000000000 : ℝ)^519 ≤ (887233071649/2000000000000 : ℝ)^391 := by
    have hnat : (5420827043 : ℕ)^519*2000000000000^391 ≤ 887233071649^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420827043 10000000000 887233071649 2000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78058077/156250000 : ℝ)^519 ≤ (19902108183539/50000000000000 : ℝ)^391 := by
    have hnat : (78058077 : ℕ)^519*50000000000000^391 ≤ 19902108183539^391*156250000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78058077 156250000 19902108183539 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24945763/100000000 : ℝ)^519 ≤ (15834130036867/100000000000000 : ℝ)^391 := by
    have hnat : (24945763 : ℕ)^519*100000000000000^391 ≤ 15834130036867^391*100000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24945763 100000000 15834130036867 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420827043/10000000000 : ℝ), (78058077/156250000 : ℝ), (-24945763/100000000 : ℝ)] ![(887233071649/2000000000000 : ℝ), (19902108183539/50000000000000 : ℝ), (15834130036867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420827043/10000000000 : ℝ)|^519 ≤ (887233071649/2000000000000 : ℝ)^391
        have hw : |(5420827043/10000000000 : ℝ)|=(5420827043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(78058077/156250000 : ℝ)|^519 ≤ (19902108183539/50000000000000 : ℝ)^391
        have hw : |(78058077/156250000 : ℝ)|=(78058077/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24945763/100000000 : ℝ)|^519 ≤ (15834130036867/100000000000000 : ℝ)^391
        have hw : |(-24945763/100000000 : ℝ)|=(24945763/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s1_3 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4320053719/10000000000 : ℝ)*x 0 + (3671191111/10000000000 : ℝ)*x 1 + (5083338801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320053719/10000000000 : ℝ)^519 ≤ (2051354902009/6250000000000 : ℝ)^391 := by
    have hnat : (4320053719 : ℕ)^519*6250000000000^391 ≤ 2051354902009^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320053719 10000000000 2051354902009 6250000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3671191111/10000000000 : ℝ)^519 ≤ (13222382658193/50000000000000 : ℝ)^391 := by
    have hnat : (3671191111 : ℕ)^519*50000000000000^391 ≤ 13222382658193^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3671191111 10000000000 13222382658193 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5083338801/10000000000 : ℝ)^519 ≤ (20366778113673/50000000000000 : ℝ)^391 := by
    have hnat : (5083338801 : ℕ)^519*50000000000000^391 ≤ 20366778113673^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083338801 10000000000 20366778113673 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320053719/10000000000 : ℝ), (3671191111/10000000000 : ℝ), (5083338801/10000000000 : ℝ)] ![(2051354902009/6250000000000 : ℝ), (13222382658193/50000000000000 : ℝ), (20366778113673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320053719/10000000000 : ℝ)|^519 ≤ (2051354902009/6250000000000 : ℝ)^391
        have hw : |(4320053719/10000000000 : ℝ)|=(4320053719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3671191111/10000000000 : ℝ)|^519 ≤ (13222382658193/50000000000000 : ℝ)^391
        have hw : |(3671191111/10000000000 : ℝ)|=(3671191111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5083338801/10000000000 : ℝ)|^519 ≤ (20366778113673/50000000000000 : ℝ)^391
        have hw : |(5083338801/10000000000 : ℝ)|=(5083338801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s1_4 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109417633/10000000000 : ℝ)*x 0 + (5005585263/10000000000 : ℝ)*x 1 + (5699803841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109417633/10000000000 : ℝ)^519 ≤ (3168520844161/25000000000000 : ℝ)^391 := by
    have hnat : (2109417633 : ℕ)^519*25000000000000^391 ≤ 3168520844161^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109417633 10000000000 3168520844161 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5005585263/10000000000 : ℝ)^519 ≤ (19954308854089/50000000000000 : ℝ)^391 := by
    have hnat : (5005585263 : ℕ)^519*50000000000000^391 ≤ 19954308854089^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5005585263 10000000000 19954308854089 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5699803841/10000000000 : ℝ)^519 ≤ (47417298903963/100000000000000 : ℝ)^391 := by
    have hnat : (5699803841 : ℕ)^519*100000000000000^391 ≤ 47417298903963^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5699803841 10000000000 47417298903963 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109417633/10000000000 : ℝ), (5005585263/10000000000 : ℝ), (5699803841/10000000000 : ℝ)] ![(3168520844161/25000000000000 : ℝ), (19954308854089/50000000000000 : ℝ), (47417298903963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109417633/10000000000 : ℝ)|^519 ≤ (3168520844161/25000000000000 : ℝ)^391
        have hw : |(-2109417633/10000000000 : ℝ)|=(2109417633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5005585263/10000000000 : ℝ)|^519 ≤ (19954308854089/50000000000000 : ℝ)^391
        have hw : |(5005585263/10000000000 : ℝ)|=(5005585263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5699803841/10000000000 : ℝ)|^519 ≤ (47417298903963/100000000000000 : ℝ)^391
        have hw : |(5699803841/10000000000 : ℝ)|=(5699803841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s1_5 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5238017721/10000000000 : ℝ)*x 0 + (-1790490399/10000000000 : ℝ)*x 1 + (1424950911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5238017721/10000000000 : ℝ)^519 ≤ (42386919167313/100000000000000 : ℝ)^391 := by
    have hnat : (5238017721 : ℕ)^519*100000000000000^391 ≤ 42386919167313^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238017721 10000000000 42386919167313 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1790490399/10000000000 : ℝ)^519 ≤ (1019578408109/10000000000000 : ℝ)^391 := by
    have hnat : (1790490399 : ℕ)^519*10000000000000^391 ≤ 1019578408109^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1790490399 10000000000 1019578408109 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1424950911/2500000000 : ℝ)^519 ≤ (4741729672859/10000000000000 : ℝ)^391 := by
    have hnat : (1424950911 : ℕ)^519*10000000000000^391 ≤ 4741729672859^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424950911 2500000000 4741729672859 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5238017721/10000000000 : ℝ), (-1790490399/10000000000 : ℝ), (1424950911/2500000000 : ℝ)] ![(42386919167313/100000000000000 : ℝ), (1019578408109/10000000000000 : ℝ), (4741729672859/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5238017721/10000000000 : ℝ)|^519 ≤ (42386919167313/100000000000000 : ℝ)^391
        have hw : |(5238017721/10000000000 : ℝ)|=(5238017721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1790490399/10000000000 : ℝ)|^519 ≤ (1019578408109/10000000000000 : ℝ)^391
        have hw : |(-1790490399/10000000000 : ℝ)|=(1790490399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1424950911/2500000000 : ℝ)|^519 ≤ (4741729672859/10000000000000 : ℝ)^391
        have hw : |(1424950911/2500000000 : ℝ)|=(1424950911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s1_6 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5238017749/10000000000 : ℝ)*x 0 + (5699803787/10000000000 : ℝ)*x 1 + (-1790490151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5238017749/10000000000 : ℝ)^519 ≤ (10596729867017/25000000000000 : ℝ)^391 := by
    have hnat : (5238017749 : ℕ)^519*25000000000000^391 ≤ 10596729867017^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238017749 10000000000 10596729867017 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5699803787/10000000000 : ℝ)^519 ≤ (11854324576917/25000000000000 : ℝ)^391 := by
    have hnat : (5699803787 : ℕ)^519*25000000000000^391 ≤ 11854324576917^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5699803787 10000000000 11854324576917 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1790490151/10000000000 : ℝ)^519 ≤ (5097891103283/50000000000000 : ℝ)^391 := by
    have hnat : (1790490151 : ℕ)^519*50000000000000^391 ≤ 5097891103283^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1790490151 10000000000 5097891103283 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5238017749/10000000000 : ℝ), (5699803787/10000000000 : ℝ), (-1790490151/10000000000 : ℝ)] ![(10596729867017/25000000000000 : ℝ), (11854324576917/25000000000000 : ℝ), (5097891103283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5238017749/10000000000 : ℝ)|^519 ≤ (10596729867017/25000000000000 : ℝ)^391
        have hw : |(5238017749/10000000000 : ℝ)|=(5238017749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5699803787/10000000000 : ℝ)|^519 ≤ (11854324576917/25000000000000 : ℝ)^391
        have hw : |(5699803787/10000000000 : ℝ)|=(5699803787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1790490151/10000000000 : ℝ)|^519 ≤ (5097891103283/50000000000000 : ℝ)^391
        have hw : |(-1790490151/10000000000 : ℝ)|=(1790490151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s1_7 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4321733557/10000000000 : ℝ)*x 0 + (202553143/400000000 : ℝ)*x 1 + (922772901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321733557/10000000000 : ℝ)^519 ≤ (1641931007177/5000000000000 : ℝ)^391 := by
    have hnat : (4321733557 : ℕ)^519*5000000000000^391 ≤ 1641931007177^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321733557 10000000000 1641931007177 5000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (202553143/400000000 : ℝ)^519 ≤ (20263084258773/50000000000000 : ℝ)^391 := by
    have hnat : (202553143 : ℕ)^519*50000000000000^391 ≤ 20263084258773^391*400000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202553143 400000000 20263084258773 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (922772901/2500000000 : ℝ)^519 ≤ (26635211319477/100000000000000 : ℝ)^391 := by
    have hnat : (922772901 : ℕ)^519*100000000000000^391 ≤ 26635211319477^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922772901 2500000000 26635211319477 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321733557/10000000000 : ℝ), (202553143/400000000 : ℝ), (922772901/2500000000 : ℝ)] ![(1641931007177/5000000000000 : ℝ), (20263084258773/50000000000000 : ℝ), (26635211319477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321733557/10000000000 : ℝ)|^519 ≤ (1641931007177/5000000000000 : ℝ)^391
        have hw : |(4321733557/10000000000 : ℝ)|=(4321733557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(202553143/400000000 : ℝ)|^519 ≤ (20263084258773/50000000000000 : ℝ)^391
        have hw : |(202553143/400000000 : ℝ)|=(202553143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(922772901/2500000000 : ℝ)|^519 ≤ (26635211319477/100000000000000 : ℝ)^391
        have hw : |(922772901/2500000000 : ℝ)|=(922772901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1111_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13967/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2737/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20579/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13967/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (57/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13967/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (57/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13967/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (57/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13967/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (57/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13967/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (57/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13967/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (57/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (57/20000 : ℝ) ^ (8303/2048 : ℝ) ≤ (300133199/6250000000000000000 : ℝ) := by
    have hpowers : (57/20000 : ℝ)^8303 ≤ (300133199/6250000000000000000 : ℝ)^2048 := by
      have hnat : (57 : ℕ)^8303*6250000000000000000^2048 ≤ 300133199^2048*20000^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57 20000 300133199 6250000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (57/20000 : ℝ)) (X := (300133199/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13967/50000 : ℝ) ^ (8303/2048 : ℝ) ≤ (284107937836581541/50000000000000000000 : ℝ) := by
    have hpowers : (13967/50000 : ℝ)^8303 ≤ (284107937836581541/50000000000000000000 : ℝ)^2048 := by
      have hnat : (13967 : ℕ)^8303*50000000000000000000^2048 ≤ 284107937836581541^2048*50000^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13967 50000 284107937836581541 50000000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13967/50000 : ℝ)) (X := (284107937836581541/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125000000300133199/3125000000000000000 : ℝ) ≤ (10000000000236897/10000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (3125000000300133199/3125000000000000000 : ℝ)^2048 ≤ (10000000000236897/10000000000000000 : ℝ)^8303 := by
      have hnat : (3125000000300133199 : ℕ)^2048*10000000000000000^8303 ≤ 10000000000236897^8303*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125000000300133199 3125000000000000000 10000000000236897 10000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000236897/10000000000000000 : ℝ)) (X := (3125000000300133199/3125000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50284107940237647133/50000000000000000000 : ℝ) ≤ (5006992795835523/5000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (50284107940237647133/50000000000000000000 : ℝ)^2048 ≤ (5006992795835523/5000000000000000 : ℝ)^8303 := by
      have hnat : (50284107940237647133 : ℕ)^2048*5000000000000000^8303 ≤ 5006992795835523^8303*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50284107940237647133 50000000000000000000 5006992795835523 5000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006992795835523/5000000000000000 : ℝ)) (X := (50284107940237647133/50000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25284107937836581541/25000000000000000000 : ℝ) ≤ (2005594236621039/2000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (25284107937836581541/25000000000000000000 : ℝ)^2048 ≤ (2005594236621039/2000000000000000 : ℝ)^8303 := by
      have hnat : (25284107937836581541 : ℕ)^2048*2000000000000000^8303 ≤ 2005594236621039^8303*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25284107937836581541 25000000000000000000 2005594236621039 2000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005594236621039/2000000000000000 : ℝ)) (X := (25284107937836581541/25000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(300133199/6250000000000000000 : ℝ) ≤ ((276482028219432500223/276490000000000000000 : ℝ)+2*(13985591434149/2764900000000000 : ℝ)*(57/20000 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (276482028219432500223/276490000000000000000 : ℝ)+2*(13985591434149/2764900000000000 : ℝ)*(57/20000 : ℝ)=(10000000000236897/10000000000000000 : ℝ) by norm_num, show 1+2*(300133199/6250000000000000000 : ℝ)=(3125000000300133199/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(284107937836581541/50000000000000000000 : ℝ)+(300133199/6250000000000000000 : ℝ) ≤ ((276482028219432500223/276490000000000000000 : ℝ)+(13985591434149/2764900000000000 : ℝ)*((13967/50000 : ℝ)+(57/20000 : ℝ)))^(8303/2048 : ℝ) := by
    rw [show (276482028219432500223/276490000000000000000 : ℝ)+(13985591434149/2764900000000000 : ℝ)*((13967/50000 : ℝ)+(57/20000 : ℝ))=(5006992795835523/5000000000000000 : ℝ) by norm_num, show 1+(284107937836581541/50000000000000000000 : ℝ)+(300133199/6250000000000000000 : ℝ)=(50284107940237647133/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(284107937836581541/50000000000000000000 : ℝ) ≤ ((276482028219432500223/276490000000000000000 : ℝ)+2*(13985591434149/2764900000000000 : ℝ)*(13967/50000 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (276482028219432500223/276490000000000000000 : ℝ)+2*(13985591434149/2764900000000000 : ℝ)*(13967/50000 : ℝ)=(2005594236621039/2000000000000000 : ℝ) by norm_num, show 1+2*(284107937836581541/50000000000000000000 : ℝ)=(25284107937836581541/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (276482028219432500223/276490000000000000000 : ℝ)*(X 1 0+X 2 0)+(13985591434149/2764900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (57/20000 : ℝ)) (hi := (13967/50000 : ℝ)) (c := (276482028219432500223/276490000000000000000 : ℝ)) (alpha := (13985591434149/2764900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (276482028219432500223/276490000000000000000 : ℝ)*(X 0 1+X 2 1)+(13985591434149/2764900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (57/20000 : ℝ)) (hi := (13967/50000 : ℝ)) (c := (276482028219432500223/276490000000000000000 : ℝ)) (alpha := (13985591434149/2764900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (276482028219432500223/276490000000000000000 : ℝ)*(X 0 2+X 1 2)+(13985591434149/2764900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (57/20000 : ℝ)) (hi := (13967/50000 : ℝ)) (c := (276482028219432500223/276490000000000000000 : ℝ)) (alpha := (13985591434149/2764900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1054283637/5000000000 : ℝ)*X 0 0+(2854934163/5000000000 : ℝ)*X 0 1+(2497859103/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((677603217/1250000000 : ℝ)*X 1 0+(-1247288217/5000000000 : ℝ)*X 1 1+(4995718163/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5420827043/10000000000 : ℝ)*X 2 0+(78058077/156250000 : ℝ)*X 2 1+(-24945763/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320053719/10000000000 : ℝ)*X 0 0+(3671191111/10000000000 : ℝ)*X 0 1+(5083338801/10000000000 : ℝ)*X 0 2+(4320053719/10000000000 : ℝ)*X 1 0+(3671191111/10000000000 : ℝ)*X 1 1+(5083338801/10000000000 : ℝ)*X 1 2+(4320053719/10000000000 : ℝ)*X 2 0+(3671191111/10000000000 : ℝ)*X 2 1+(5083338801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2109417633/10000000000 : ℝ)*X 0 0+(5005585263/10000000000 : ℝ)*X 0 1+(5699803841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5238017721/10000000000 : ℝ)*X 1 0+(-1790490399/10000000000 : ℝ)*X 1 1+(1424950911/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5238017749/10000000000 : ℝ)*X 2 0+(5699803787/10000000000 : ℝ)*X 2 1+(-1790490151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4321733557/10000000000 : ℝ)*X 0 0+(202553143/400000000 : ℝ)*X 0 1+(922772901/2500000000 : ℝ)*X 0 2+(4321733557/10000000000 : ℝ)*X 1 0+(202553143/400000000 : ℝ)*X 1 1+(922772901/2500000000 : ℝ)*X 1 2+(4321733557/10000000000 : ℝ)*X 2 0+(202553143/400000000 : ℝ)*X 2 1+(922772901/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53879614758702269041072052919/6912250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68255297/25000000000000 : ℝ)*(base1) + (366079623/25000000000000 : ℝ)*(base19) + (1801935129/100000000000000 : ℝ)*(base23) + (75883831/100000000000000 : ℝ)*(upper3) + (53315699/25000000000000 : ℝ)*(upper5) + (527106230911583/50000000000000 : ℝ)*(major0) + (527106230911583/50000000000000 : ℝ)*(major1) + (527106230911583/50000000000000 : ℝ)*(major2) + (700135469537583/50000000000000 : ℝ)*(sp0) + (1400276508908067/100000000000000 : ℝ)*(sp1) + (140027617129143/10000000000000 : ℝ)*(sp2) + (708143909814959/100000000000000 : ℝ)*(sp3) + (3653586291/50000000000000 : ℝ)*(sp4) + (2507756911/100000000000000 : ℝ)*(sp7) + (354073345296529/50000000000000 : ℝ)*(f.failure) + (4375868666333/312500000000 : ℝ)*(f.sum) + (22444737031869/34561250000000000000000000000 : ℝ)*base66 + (75953685612955483009/13824500000000000000000000000000000 : ℝ)*base67 + (42407892072132983009/13824500000000000000000000000000000 : ℝ)*base69 + (66006338470057483009/13824500000000000000000000000000000 : ℝ)*base71 + (51745222969857/69122500000000000000000000000 : ℝ)*base73 + (66089796091789483009/13824500000000000000000000000000000 : ℝ)*base75 + (50432635848796483009/13824500000000000000000000000000000 : ℝ)*base77 + (107212596314034483009/13824500000000000000000000000000000 : ℝ)*base79 + (102326117932999/138245000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13766091/5000000000000000000000 : ℝ)*base90 + (13766091/5000000000000000000000 : ℝ)*base92 + (13766091/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17938980127321047856045908909/3456125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63437307/100000000000000 : ℝ)*(base1) + (1166292611/100000000000000 : ℝ)*(base19) + (1191272663/100000000000000 : ℝ)*(base23) + (113110329/100000000000000 : ℝ)*(upper3) + (28908589/25000000000000 : ℝ)*(upper5) + (542235116039961/50000000000000 : ℝ)*(major0) + (542235116039961/50000000000000 : ℝ)*(major1) + (542235116039961/50000000000000 : ℝ)*(major2) + (460005429/10000000000000 : ℝ)*(sp1) + (1019028789/20000000000000 : ℝ)*(sp2) + (720234298041769/50000000000000 : ℝ)*(sp4) + (144046276629933/10000000000000 : ℝ)*(sp5) + (720231123114811/50000000000000 : ℝ)*(sp6) + (364235847529993/50000000000000 : ℝ)*(sp7) + (364235879248647/50000000000000 : ℝ)*(f.failure) + (144046853264623/10000000000000 : ℝ)*(f.sum) + (67360607546809/69122500000000000000000000000 : ℝ)*base65 + (63966584062249688697/13824500000000000000000000000000000 : ℝ)*base68 + (95110784813320688697/13824500000000000000000000000000000 : ℝ)*base70 + (53415506239785688697/13824500000000000000000000000000000 : ℝ)*base72 + (108227185215761/69122500000000000000000000000 : ℝ)*base74 + (114721644474054688697/13824500000000000000000000000000000 : ℝ)*base76 + (40138886976189188697/13824500000000000000000000000000000 : ℝ)*base78 + (1690404378740311303/13824500000000000000000000000000000 : ℝ)*base79 + (29718924190907/8640312500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (44193987/5000000000000000000000 : ℝ)*base89 + (44193987/5000000000000000000000 : ℝ)*base91 + (44193987/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1111_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13967/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2737/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20579/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1111_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1111_s2_0 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2163480201/10000000000 : ℝ)*x 0 + (2758404591/5000000000 : ℝ)*x 1 + (5153891287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163480201/10000000000 : ℝ)^519 ≤ (524281784753/4000000000000 : ℝ)^391 := by
    have hnat : (2163480201 : ℕ)^519*4000000000000^391 ≤ 524281784753^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163480201 10000000000 524281784753 4000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2758404591/5000000000 : ℝ)^519 ≤ (22703638264017/50000000000000 : ℝ)^391 := by
    have hnat : (2758404591 : ℕ)^519*50000000000000^391 ≤ 22703638264017^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758404591 5000000000 22703638264017 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5153891287/10000000000 : ℝ)^519 ≤ (8297135769599/20000000000000 : ℝ)^391 := by
    have hnat : (5153891287 : ℕ)^519*20000000000000^391 ≤ 8297135769599^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153891287 10000000000 8297135769599 20000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2163480201/10000000000 : ℝ), (2758404591/5000000000 : ℝ), (5153891287/10000000000 : ℝ)] ![(524281784753/4000000000000 : ℝ), (22703638264017/50000000000000 : ℝ), (8297135769599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2163480201/10000000000 : ℝ)|^519 ≤ (524281784753/4000000000000 : ℝ)^391
        have hw : |(-2163480201/10000000000 : ℝ)|=(2163480201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2758404591/5000000000 : ℝ)|^519 ≤ (22703638264017/50000000000000 : ℝ)^391
        have hw : |(2758404591/5000000000 : ℝ)|=(2758404591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5153891287/10000000000 : ℝ)|^519 ≤ (8297135769599/20000000000000 : ℝ)^391
        have hw : |(5153891287/10000000000 : ℝ)|=(5153891287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s2_1 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5375207403/10000000000 : ℝ)*x 0 + (-2352394027/10000000000 : ℝ)*x 1 + (1030778513/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375207403/10000000000 : ℝ)^519 ≤ (21933395370243/50000000000000 : ℝ)^391 := by
    have hnat : (5375207403 : ℕ)^519*50000000000000^391 ≤ 21933395370243^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375207403 10000000000 21933395370243 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2352394027/10000000000 : ℝ)^519 ≤ (14647516750071/100000000000000 : ℝ)^391 := by
    have hnat : (2352394027 : ℕ)^519*100000000000000^391 ≤ 14647516750071^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2352394027 10000000000 14647516750071 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030778513/2000000000 : ℝ)^519 ≤ (20742846251383/50000000000000 : ℝ)^391 := by
    have hnat : (1030778513 : ℕ)^519*50000000000000^391 ≤ 20742846251383^391*2000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030778513 2000000000 20742846251383 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375207403/10000000000 : ℝ), (-2352394027/10000000000 : ℝ), (1030778513/2000000000 : ℝ)] ![(21933395370243/50000000000000 : ℝ), (14647516750071/100000000000000 : ℝ), (20742846251383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375207403/10000000000 : ℝ)|^519 ≤ (21933395370243/50000000000000 : ℝ)^391
        have hw : |(5375207403/10000000000 : ℝ)|=(5375207403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2352394027/10000000000 : ℝ)|^519 ≤ (14647516750071/100000000000000 : ℝ)^391
        have hw : |(-2352394027/10000000000 : ℝ)|=(2352394027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030778513/2000000000 : ℝ)|^519 ≤ (20742846251383/50000000000000 : ℝ)^391
        have hw : |(1030778513/2000000000 : ℝ)|=(1030778513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s2_2 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1075041469/2000000000 : ℝ)*x 0 + (5153892623/10000000000 : ℝ)*x 1 + (-1176197013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075041469/2000000000 : ℝ)^519 ≤ (43866790112197/100000000000000 : ℝ)^391 := by
    have hnat : (1075041469 : ℕ)^519*100000000000000^391 ≤ 43866790112197^391*2000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075041469 2000000000 43866790112197 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5153892623/10000000000 : ℝ)^519 ≤ (20742846561233/50000000000000 : ℝ)^391 := by
    have hnat : (5153892623 : ℕ)^519*50000000000000^391 ≤ 20742846561233^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153892623 10000000000 20742846561233 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1176197013/5000000000 : ℝ)^519 ≤ (7323758370903/50000000000000 : ℝ)^391 := by
    have hnat : (1176197013 : ℕ)^519*50000000000000^391 ≤ 7323758370903^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1176197013 5000000000 7323758370903 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075041469/2000000000 : ℝ), (5153892623/10000000000 : ℝ), (-1176197013/5000000000 : ℝ)] ![(43866790112197/100000000000000 : ℝ), (20742846561233/50000000000000 : ℝ), (7323758370903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075041469/2000000000 : ℝ)|^519 ≤ (43866790112197/100000000000000 : ℝ)^391
        have hw : |(1075041469/2000000000 : ℝ)|=(1075041469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5153892623/10000000000 : ℝ)|^519 ≤ (20742846561233/50000000000000 : ℝ)^391
        have hw : |(5153892623/10000000000 : ℝ)|=(5153892623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1176197013/5000000000 : ℝ)|^519 ≤ (7323758370903/50000000000000 : ℝ)^391
        have hw : |(-1176197013/5000000000 : ℝ)|=(1176197013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s2_3 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (435764533/1000000000 : ℝ)*x 0 + (501697127/1250000000 : ℝ)*x 1 + (4731202313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435764533/1000000000 : ℝ)^519 ≤ (16600658404183/50000000000000 : ℝ)^391 := by
    have hnat : (435764533 : ℕ)^519*50000000000000^391 ≤ 16600658404183^391*1000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435764533 1000000000 16600658404183 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501697127/1250000000 : ℝ)^519 ≤ (1488371820649/5000000000000 : ℝ)^391 := by
    have hnat : (501697127 : ℕ)^519*5000000000000^391 ≤ 1488371820649^391*1250000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501697127 1250000000 1488371820649 5000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4731202313/10000000000 : ℝ)^519 ≤ (1481249870539/4000000000000 : ℝ)^391 := by
    have hnat : (4731202313 : ℕ)^519*4000000000000^391 ≤ 1481249870539^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4731202313 10000000000 1481249870539 4000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435764533/1000000000 : ℝ), (501697127/1250000000 : ℝ), (4731202313/10000000000 : ℝ)] ![(16600658404183/50000000000000 : ℝ), (1488371820649/5000000000000 : ℝ), (1481249870539/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435764533/1000000000 : ℝ)|^519 ≤ (16600658404183/50000000000000 : ℝ)^391
        have hw : |(435764533/1000000000 : ℝ)|=(435764533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501697127/1250000000 : ℝ)|^519 ≤ (1488371820649/5000000000000 : ℝ)^391
        have hw : |(501697127/1250000000 : ℝ)|=(501697127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4731202313/10000000000 : ℝ)|^519 ≤ (1481249870539/4000000000000 : ℝ)^391
        have hw : |(4731202313/10000000000 : ℝ)|=(4731202313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s2_4 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2163591461/10000000000 : ℝ)*x 0 + (5156449129/10000000000 : ℝ)*x 1 + (344639087/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163591461/10000000000 : ℝ)^519 ≤ (1638492416843/12500000000000 : ℝ)^391 := by
    have hnat : (2163591461 : ℕ)^519*12500000000000^391 ≤ 1638492416843^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163591461 10000000000 1638492416843 12500000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5156449129/10000000000 : ℝ)^519 ≤ (4151301028943/10000000000000 : ℝ)^391 := by
    have hnat : (5156449129 : ℕ)^519*10000000000000^391 ≤ 4151301028943^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5156449129 10000000000 4151301028943 10000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (344639087/625000000 : ℝ)^519 ≤ (2836190647157/6250000000000 : ℝ)^391 := by
    have hnat : (344639087 : ℕ)^519*6250000000000^391 ≤ 2836190647157^391*625000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344639087 625000000 2836190647157 6250000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2163591461/10000000000 : ℝ), (5156449129/10000000000 : ℝ), (344639087/625000000 : ℝ)] ![(1638492416843/12500000000000 : ℝ), (4151301028943/10000000000000 : ℝ), (2836190647157/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2163591461/10000000000 : ℝ)|^519 ≤ (1638492416843/12500000000000 : ℝ)^391
        have hw : |(-2163591461/10000000000 : ℝ)|=(2163591461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5156449129/10000000000 : ℝ)|^519 ≤ (4151301028943/10000000000000 : ℝ)^391
        have hw : |(5156449129/10000000000 : ℝ)|=(5156449129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(344639087/625000000 : ℝ)|^519 ≤ (2836190647157/6250000000000 : ℝ)^391
        have hw : |(344639087/625000000 : ℝ)|=(344639087/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s2_5 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5283317693/10000000000 : ℝ)*x 0 + (-1992060581/10000000000 : ℝ)*x 1 + (1378556369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283317693/10000000000 : ℝ)^519 ≤ (42874185695843/100000000000000 : ℝ)^391 := by
    have hnat : (5283317693 : ℕ)^519*100000000000000^391 ≤ 42874185695843^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283317693 10000000000 42874185695843 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1992060581/10000000000 : ℝ)^519 ≤ (2936690756291/25000000000000 : ℝ)^391 := by
    have hnat : (1992060581 : ℕ)^519*25000000000000^391 ≤ 2936690756291^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992060581 10000000000 2936690756291 25000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1378556369/2500000000 : ℝ)^519 ≤ (22689525636043/50000000000000 : ℝ)^391 := by
    have hnat : (1378556369 : ℕ)^519*50000000000000^391 ≤ 22689525636043^391*2500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378556369 2500000000 22689525636043 50000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283317693/10000000000 : ℝ), (-1992060581/10000000000 : ℝ), (1378556369/2500000000 : ℝ)] ![(42874185695843/100000000000000 : ℝ), (2936690756291/25000000000000 : ℝ), (22689525636043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283317693/10000000000 : ℝ)|^519 ≤ (42874185695843/100000000000000 : ℝ)^391
        have hw : |(5283317693/10000000000 : ℝ)|=(5283317693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1992060581/10000000000 : ℝ)|^519 ≤ (2936690756291/25000000000000 : ℝ)^391
        have hw : |(-1992060581/10000000000 : ℝ)|=(1992060581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1378556369/2500000000 : ℝ)|^519 ≤ (22689525636043/50000000000000 : ℝ)^391
        have hw : |(1378556369/2500000000 : ℝ)|=(1378556369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s2_6 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2641658913/5000000000 : ℝ)*x 0 + (5514225423/10000000000 : ℝ)*x 1 + (-249007559/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2641658913/5000000000 : ℝ)^519 ≤ (2679636695529/6250000000000 : ℝ)^391 := by
    have hnat : (2641658913 : ℕ)^519*6250000000000^391 ≤ 2679636695529^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641658913 5000000000 2679636695529 6250000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5514225423/10000000000 : ℝ)^519 ≤ (2268952534657/5000000000000 : ℝ)^391 := by
    have hnat : (5514225423 : ℕ)^519*5000000000000^391 ≤ 2268952534657^391*10000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514225423 10000000000 2268952534657 5000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249007559/1250000000 : ℝ)^519 ≤ (2936690543/25000000000 : ℝ)^391 := by
    have hnat : (249007559 : ℕ)^519*25000000000^391 ≤ 2936690543^391*1250000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249007559 1250000000 2936690543 25000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2641658913/5000000000 : ℝ), (5514225423/10000000000 : ℝ), (-249007559/1250000000 : ℝ)] ![(2679636695529/6250000000000 : ℝ), (2268952534657/5000000000000 : ℝ), (2936690543/25000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2641658913/5000000000 : ℝ)|^519 ≤ (2679636695529/6250000000000 : ℝ)^391
        have hw : |(2641658913/5000000000 : ℝ)|=(2641658913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5514225423/10000000000 : ℝ)|^519 ≤ (2268952534657/5000000000000 : ℝ)^391
        have hw : |(5514225423/10000000000 : ℝ)|=(5514225423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249007559/1250000000 : ℝ)|^519 ≤ (2936690543/25000000000 : ℝ)^391
        have hw : |(-249007559/1250000000 : ℝ)|=(249007559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1111_s2_7 (p : ℝ) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2178933347/5000000000 : ℝ)*x 0 + (590768209/1250000000 : ℝ)*x 1 + (200934201/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178933347/5000000000 : ℝ)^519 ≤ (2075222222087/6250000000000 : ℝ)^391 := by
    have hnat : (2178933347 : ℕ)^519*6250000000000^391 ≤ 2075222222087^391*5000000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178933347 5000000000 2075222222087 6250000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (590768209/1250000000 : ℝ)^519 ≤ (36978720859483/100000000000000 : ℝ)^391 := by
    have hnat : (590768209 : ℕ)^519*100000000000000^391 ≤ 36978720859483^391*1250000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590768209 1250000000 36978720859483 100000000000000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200934201/500000000 : ℝ)^519 ≤ (2911887067/9765625000 : ℝ)^391 := by
    have hnat : (200934201 : ℕ)^519*9765625000^391 ≤ 2911887067^391*500000000^519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200934201 500000000 2911887067 9765625000 519 391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (519/128 : ℝ)) 519 391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178933347/5000000000 : ℝ), (590768209/1250000000 : ℝ), (200934201/500000000 : ℝ)] ![(2075222222087/6250000000000 : ℝ), (36978720859483/100000000000000 : ℝ), (2911887067/9765625000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178933347/5000000000 : ℝ)|^519 ≤ (2075222222087/6250000000000 : ℝ)^391
        have hw : |(2178933347/5000000000 : ℝ)|=(2178933347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(590768209/1250000000 : ℝ)|^519 ≤ (36978720859483/100000000000000 : ℝ)^391
        have hw : |(590768209/1250000000 : ℝ)|=(590768209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(200934201/500000000 : ℝ)|^519 ≤ (2911887067/9765625000 : ℝ)^391
        have hw : |(200934201/500000000 : ℝ)|=(200934201/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1111_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20579/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2737/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (279/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16597/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20579/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2737/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20579/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2737/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20579/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2737/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20579/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2737/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20579/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2737/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20579/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2737/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (2737/50000 : ℝ) ^ (8303/2048 : ℝ) ≤ (383536130308149/50000000000000000000 : ℝ) := by
    have hpowers : (2737/50000 : ℝ)^8303 ≤ (383536130308149/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2737 : ℕ)^8303*50000000000000000000^2048 ≤ 383536130308149^2048*50000^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2737 50000 383536130308149 50000000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2737/50000 : ℝ)) (X := (383536130308149/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20579/100000 : ℝ) ^ (8303/2048 : ℝ) ≤ (164620986671195249/100000000000000000000 : ℝ) := by
    have hpowers : (20579/100000 : ℝ)^8303 ≤ (164620986671195249/100000000000000000000 : ℝ)^2048 := by
      have hnat : (20579 : ℕ)^8303*100000000000000000000^2048 ≤ 164620986671195249^2048*100000^8303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20579 100000 164620986671195249 100000000000000000000 8303 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20579/100000 : ℝ)) (X := (164620986671195249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000383536130308149/25000000000000000000 : ℝ) ≤ (10000037840657877/10000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (25000383536130308149/25000000000000000000 : ℝ)^2048 ≤ (10000037840657877/10000000000000000 : ℝ)^8303 := by
      have hnat : (25000383536130308149 : ℕ)^2048*10000000000000000^8303 ≤ 10000037840657877^8303*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000383536130308149 25000000000000000000 10000037840657877 10000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000037840657877/10000000000000000 : ℝ)) (X := (25000383536130308149/25000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100165388058931811547/100000000000000000000 : ℝ) ≤ (2501019221786221/2500000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (100165388058931811547/100000000000000000000 : ℝ)^2048 ≤ (2501019221786221/2500000000000000 : ℝ)^8303 := by
      have hnat : (100165388058931811547 : ℕ)^2048*2500000000000000^8303 ≤ 2501019221786221^8303*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100165388058931811547 100000000000000000000 2501019221786221 2500000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501019221786221/2500000000000000 : ℝ)) (X := (100165388058931811547/100000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50164620986671195249/50000000000000000000 : ℝ) ≤ (10008115933631891/10000000000000000 : ℝ) ^ (8303/2048 : ℝ) := by
    have hpowers : (50164620986671195249/50000000000000000000 : ℝ)^2048 ≤ (10008115933631891/10000000000000000 : ℝ)^8303 := by
      have hnat : (50164620986671195249 : ℕ)^2048*10000000000000000^8303 ≤ 10008115933631891^8303*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50164620986671195249 50000000000000000000 10008115933631891 10000000000000000 2048 8303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008115933631891/10000000000000000 : ℝ)) (X := (50164620986671195249/50000000000000000000 : ℝ)) (by norm_num) 8303 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(383536130308149/50000000000000000000 : ℝ) ≤ ((7947702742220919971/7950000000000000000 : ℝ)+2*(212581394053/79500000000000 : ℝ)*(2737/50000 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (7947702742220919971/7950000000000000000 : ℝ)+2*(212581394053/79500000000000 : ℝ)*(2737/50000 : ℝ)=(10000037840657877/10000000000000000 : ℝ) by norm_num, show 1+2*(383536130308149/50000000000000000000 : ℝ)=(25000383536130308149/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(164620986671195249/100000000000000000000 : ℝ)+(383536130308149/50000000000000000000 : ℝ) ≤ ((7947702742220919971/7950000000000000000 : ℝ)+(212581394053/79500000000000 : ℝ)*((20579/100000 : ℝ)+(2737/50000 : ℝ)))^(8303/2048 : ℝ) := by
    rw [show (7947702742220919971/7950000000000000000 : ℝ)+(212581394053/79500000000000 : ℝ)*((20579/100000 : ℝ)+(2737/50000 : ℝ))=(2501019221786221/2500000000000000 : ℝ) by norm_num, show 1+(164620986671195249/100000000000000000000 : ℝ)+(383536130308149/50000000000000000000 : ℝ)=(100165388058931811547/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(164620986671195249/100000000000000000000 : ℝ) ≤ ((7947702742220919971/7950000000000000000 : ℝ)+2*(212581394053/79500000000000 : ℝ)*(20579/100000 : ℝ))^(8303/2048 : ℝ) := by
    rw [show (7947702742220919971/7950000000000000000 : ℝ)+2*(212581394053/79500000000000 : ℝ)*(20579/100000 : ℝ)=(10008115933631891/10000000000000000 : ℝ) by norm_num, show 1+2*(164620986671195249/100000000000000000000 : ℝ)=(50164620986671195249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7947702742220919971/7950000000000000000 : ℝ)*(X 1 0+X 2 0)+(212581394053/79500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (2737/50000 : ℝ)) (hi := (20579/100000 : ℝ)) (c := (7947702742220919971/7950000000000000000 : ℝ)) (alpha := (212581394053/79500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7947702742220919971/7950000000000000000 : ℝ)*(X 0 1+X 2 1)+(212581394053/79500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (2737/50000 : ℝ)) (hi := (20579/100000 : ℝ)) (c := (7947702742220919971/7950000000000000000 : ℝ)) (alpha := (212581394053/79500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7947702742220919971/7950000000000000000 : ℝ)*(X 0 2+X 1 2)+(212581394053/79500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8303/2048 : ℝ)) (lo := (2737/50000 : ℝ)) (hi := (20579/100000 : ℝ)) (c := (7947702742220919971/7950000000000000000 : ℝ)) (alpha := (212581394053/79500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2163480201/10000000000 : ℝ)*X 0 0+(2758404591/5000000000 : ℝ)*X 0 1+(5153891287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5375207403/10000000000 : ℝ)*X 1 0+(-2352394027/10000000000 : ℝ)*X 1 1+(1030778513/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1075041469/2000000000 : ℝ)*X 2 0+(5153892623/10000000000 : ℝ)*X 2 1+(-1176197013/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((435764533/1000000000 : ℝ)*X 0 0+(501697127/1250000000 : ℝ)*X 0 1+(4731202313/10000000000 : ℝ)*X 0 2+(435764533/1000000000 : ℝ)*X 1 0+(501697127/1250000000 : ℝ)*X 1 1+(4731202313/10000000000 : ℝ)*X 1 2+(435764533/1000000000 : ℝ)*X 2 0+(501697127/1250000000 : ℝ)*X 2 1+(4731202313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2163591461/10000000000 : ℝ)*X 0 0+(5156449129/10000000000 : ℝ)*X 0 1+(344639087/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5283317693/10000000000 : ℝ)*X 1 0+(-1992060581/10000000000 : ℝ)*X 1 1+(1378556369/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2641658913/5000000000 : ℝ)*X 2 0+(5514225423/10000000000 : ℝ)*X 2 1+(-249007559/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178933347/5000000000 : ℝ)*X 0 0+(590768209/1250000000 : ℝ)*X 0 1+(200934201/500000000 : ℝ)*X 0 2+(2178933347/5000000000 : ℝ)*X 1 0+(590768209/1250000000 : ℝ)*X 1 1+(200934201/500000000 : ℝ)*X 1 2+(2178933347/5000000000 : ℝ)*X 2 0+(590768209/1250000000 : ℝ)*X 2 1+(200934201/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1111_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82169854238805672509452049/26500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76302607/100000000000000 : ℝ)*(base29) + (92322381/100000000000000 : ℝ)*(upper2) + (3161937/50000000000000 : ℝ)*(upper3) + (19085177/25000000000000 : ℝ)*(upper4) + (2265249/10000000000000 : ℝ)*(upper5) + (2074474436741691/100000000000000 : ℝ)*(major0) + (1037237256522149/50000000000000 : ℝ)*(major1) + (1037237256522149/50000000000000 : ℝ)*(major2) + (1377726278535533/50000000000000 : ℝ)*(sp0) + (2755460992384089/100000000000000 : ℝ)*(sp1) + (275546099238409/10000000000000 : ℝ)*(sp2) + (1393486468448679/100000000000000 : ℝ)*(sp3) + (8511615629/100000000000000 : ℝ)*(sp4) + (173199363/12500000000000 : ℝ)*(sp7) + (696743927021791/50000000000000 : ℝ)*(f.failure) + (344432633585837/12500000000000 : ℝ)*(f.sum) + (25590989128931/3975000000000000000000000000 : ℝ)*base66 + (689691130990045893/132500000000000000000000000000000 : ℝ)*base67 + (185104682400045893/132500000000000000000000000000000 : ℝ)*base69 + (9397570850145389039/795000000000000000000000000000000 : ℝ)*base72 + (10571351221133/7950000000000000000000000000 : ℝ)*base74 + (5108300089329087679/397500000000000000000000000000000 : ℝ)*base75 + (7662030345630389039/795000000000000000000000000000000 : ℝ)*base78 + (297811323654087679/397500000000000000000000000000000 : ℝ)*base79 + (36408861699233/7950000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (23805189/5000000000000000000000 : ℝ)*base90 + (23805189/5000000000000000000000 : ℝ)*base92 + (23805189/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1072656060962515573745021403/132500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1621743113/100000000000000 : ℝ)*(base19) + (57798023/3125000000000 : ℝ)*(base23) + (107161327/50000000000000 : ℝ)*(upper3) + (56947393/100000000000000 : ℝ)*(lower4) + (156887921/100000000000000 : ℝ)*(upper5) + (2104273296922807/100000000000000 : ℝ)*(major0) + (2104273296922807/100000000000000 : ℝ)*(major1) + (2104273296922807/100000000000000 : ℝ)*(major2) + (14892702649/100000000000000 : ℝ)*(sp1) + (2218394971/12500000000000 : ℝ)*(sp2) + (349380214651013/12500000000000 : ℝ)*(sp4) + (2795025202762343/100000000000000 : ℝ)*(sp5) + (6987555301279/250000000000 : ℝ)*(sp6) + (353376151696731/25000000000000 : ℝ)*(sp7) + (353376151696731/25000000000000 : ℝ)*(f.failure) + (349380214651013/12500000000000 : ℝ)*(f.sum) + (11265449648429/3975000000000000000000000000 : ℝ)*base66 + (1311641412702926199/265000000000000000000000000000000 : ℝ)*base67 + (1166872733142926199/265000000000000000000000000000000 : ℝ)*base69 + (299060429167073801/265000000000000000000000000000000 : ℝ)*base72 + (1775951268179/3975000000000000000000000000 : ℝ)*base74 + (2107461485882073801/265000000000000000000000000000000 : ℝ)*base76 + (884606507622926199/265000000000000000000000000000000 : ℝ)*base77 + (1364255347982926199/265000000000000000000000000000000 : ℝ)*base79 + (1946555048429/3975000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2783449/2500000000000000000000 : ℝ)*base90 + (2783449/2500000000000000000000 : ℝ)*base92 + (2783449/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1111_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20579/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2737/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16597/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1111_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1111_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16597/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1111_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1111_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1111_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8303/2048 : ℝ) ≤ p) (hpb : p ≤ (519/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148869221/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16597/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1111_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

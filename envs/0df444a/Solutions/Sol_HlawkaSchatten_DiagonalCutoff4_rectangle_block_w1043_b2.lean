-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1043_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:49:26.893934+00:00
-- url     : https://prove2.me/submissions/e3a644b2-1698-4ea5-ab86-f80af0617351

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
theorem support_rectangle_w1043_s6_0 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-27688583/125000000 : ℝ)*x 0 + (2697696579/5000000000 : ℝ)*x 1 + (5263423041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27688583/125000000 : ℝ)^2059 ≤ (3362630697631/25000000000000 : ℝ)^1547 := by
    have hnat : (27688583 : ℕ)^2059*25000000000000^1547 ≤ 3362630697631^1547*125000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27688583 125000000 3362630697631 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697696579/5000000000 : ℝ)^2059 ≤ (21993918935297/50000000000000 : ℝ)^1547 := by
    have hnat : (2697696579 : ℕ)^2059*50000000000000^1547 ≤ 21993918935297^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697696579 5000000000 21993918935297 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263423041/10000000000 : ℝ)^2059 ≤ (10640409830739/25000000000000 : ℝ)^1547 := by
    have hnat : (5263423041 : ℕ)^2059*25000000000000^1547 ≤ 10640409830739^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263423041 10000000000 10640409830739 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27688583/125000000 : ℝ), (2697696579/5000000000 : ℝ), (5263423041/10000000000 : ℝ)] ![(3362630697631/25000000000000 : ℝ), (21993918935297/50000000000000 : ℝ), (10640409830739/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27688583/125000000 : ℝ)|^2059 ≤ (3362630697631/25000000000000 : ℝ)^1547
        have hw : |(-27688583/125000000 : ℝ)|=(27688583/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697696579/5000000000 : ℝ)|^2059 ≤ (21993918935297/50000000000000 : ℝ)^1547
        have hw : |(2697696579/5000000000 : ℝ)|=(2697696579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263423041/10000000000 : ℝ)|^2059 ≤ (10640409830739/25000000000000 : ℝ)^1547
        have hw : |(5263423041/10000000000 : ℝ)|=(5263423041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s6_1 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345186373/10000000000 : ℝ)*x 0 + (-45641193/200000000 : ℝ)*x 1 + (1315855757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345186373/10000000000 : ℝ)^2059 ≤ (43443877465647/100000000000000 : ℝ)^1547 := by
    have hnat : (5345186373 : ℕ)^2059*100000000000000^1547 ≤ 43443877465647^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345186373 10000000000 43443877465647 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45641193/200000000 : ℝ)^2059 ≤ (3498620833497/25000000000000 : ℝ)^1547 := by
    have hnat : (45641193 : ℕ)^2059*25000000000000^1547 ≤ 3498620833497^1547*200000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45641193 200000000 3498620833497 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315855757/2500000000 : ℝ)^2059 ≤ (42561639183043/100000000000000 : ℝ)^1547 := by
    have hnat : (1315855757 : ℕ)^2059*100000000000000^1547 ≤ 42561639183043^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315855757 2500000000 42561639183043 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345186373/10000000000 : ℝ), (-45641193/200000000 : ℝ), (1315855757/2500000000 : ℝ)] ![(43443877465647/100000000000000 : ℝ), (3498620833497/25000000000000 : ℝ), (42561639183043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345186373/10000000000 : ℝ)|^2059 ≤ (43443877465647/100000000000000 : ℝ)^1547
        have hw : |(5345186373/10000000000 : ℝ)|=(5345186373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45641193/200000000 : ℝ)|^2059 ≤ (3498620833497/25000000000000 : ℝ)^1547
        have hw : |(-45641193/200000000 : ℝ)|=(45641193/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315855757/2500000000 : ℝ)|^2059 ≤ (42561639183043/100000000000000 : ℝ)^1547
        have hw : |(1315855757/2500000000 : ℝ)|=(1315855757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s6_2 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672593113/5000000000 : ℝ)*x 0 + (5263423129/10000000000 : ℝ)*x 1 + (-35657183/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672593113/5000000000 : ℝ)^2059 ≤ (339405280277/781250000000 : ℝ)^1547 := by
    have hnat : (2672593113 : ℕ)^2059*781250000000^1547 ≤ 339405280277^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672593113 5000000000 339405280277 781250000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263423129/10000000000 : ℝ)^2059 ≤ (21280820135031/50000000000000 : ℝ)^1547 := by
    have hnat : (5263423129 : ℕ)^2059*50000000000000^1547 ≤ 21280820135031^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263423129 10000000000 21280820135031 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35657183/156250000 : ℝ)^2059 ≤ (13994483840031/100000000000000 : ℝ)^1547 := by
    have hnat : (35657183 : ℕ)^2059*100000000000000^1547 ≤ 13994483840031^1547*156250000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35657183 156250000 13994483840031 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672593113/5000000000 : ℝ), (5263423129/10000000000 : ℝ), (-35657183/156250000 : ℝ)] ![(339405280277/781250000000 : ℝ), (21280820135031/50000000000000 : ℝ), (13994483840031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672593113/5000000000 : ℝ)|^2059 ≤ (339405280277/781250000000 : ℝ)^1547
        have hw : |(2672593113/5000000000 : ℝ)|=(2672593113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263423129/10000000000 : ℝ)|^2059 ≤ (21280820135031/50000000000000 : ℝ)^1547
        have hw : |(5263423129/10000000000 : ℝ)|=(5263423129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35657183/156250000 : ℝ)|^2059 ≤ (13994483840031/100000000000000 : ℝ)^1547
        have hw : |(-35657183/156250000 : ℝ)|=(35657183/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s6_3 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4378778719/10000000000 : ℝ)*x 0 + (4251974839/10000000000 : ℝ)*x 1 + (563679707/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378778719/10000000000 : ℝ)^2059 ≤ (4164511530269/12500000000000 : ℝ)^1547 := by
    have hnat : (4378778719 : ℕ)^2059*12500000000000^1547 ≤ 4164511530269^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378778719 10000000000 4164511530269 12500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4251974839/10000000000 : ℝ)^2059 ≤ (32038183739009/100000000000000 : ℝ)^1547 := by
    have hnat : (4251974839 : ℕ)^2059*100000000000000^1547 ≤ 32038183739009^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251974839 10000000000 32038183739009 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563679707/1250000000 : ℝ)^2059 ≤ (34645723993943/100000000000000 : ℝ)^1547 := by
    have hnat : (563679707 : ℕ)^2059*100000000000000^1547 ≤ 34645723993943^1547*1250000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563679707 1250000000 34645723993943 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378778719/10000000000 : ℝ), (4251974839/10000000000 : ℝ), (563679707/1250000000 : ℝ)] ![(4164511530269/12500000000000 : ℝ), (32038183739009/100000000000000 : ℝ), (34645723993943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378778719/10000000000 : ℝ)|^2059 ≤ (4164511530269/12500000000000 : ℝ)^1547
        have hw : |(4378778719/10000000000 : ℝ)|=(4378778719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4251974839/10000000000 : ℝ)|^2059 ≤ (32038183739009/100000000000000 : ℝ)^1547
        have hw : |(4251974839/10000000000 : ℝ)|=(4251974839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563679707/1250000000 : ℝ)|^2059 ≤ (34645723993943/100000000000000 : ℝ)^1547
        have hw : |(563679707/1250000000 : ℝ)|=(563679707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s6_4 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2215091927/10000000000 : ℝ)*x 0 + (2631878199/5000000000 : ℝ)*x 1 + (2697529289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2215091927/10000000000 : ℝ)^2059 ≤ (2690113103929/20000000000000 : ℝ)^1547 := by
    have hnat : (2215091927 : ℕ)^2059*20000000000000^1547 ≤ 2690113103929^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215091927 10000000000 2690113103929 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631878199/5000000000 : ℝ)^2059 ≤ (5320653392443/12500000000000 : ℝ)^1547 := by
    have hnat : (2631878199 : ℕ)^2059*12500000000000^1547 ≤ 5320653392443^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631878199 5000000000 5320653392443 12500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697529289/5000000000 : ℝ)^2059 ≤ (43984207331883/100000000000000 : ℝ)^1547 := by
    have hnat : (2697529289 : ℕ)^2059*100000000000000^1547 ≤ 43984207331883^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697529289 5000000000 43984207331883 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2215091927/10000000000 : ℝ), (2631878199/5000000000 : ℝ), (2697529289/5000000000 : ℝ)] ![(2690113103929/20000000000000 : ℝ), (5320653392443/12500000000000 : ℝ), (43984207331883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2215091927/10000000000 : ℝ)|^2059 ≤ (2690113103929/20000000000000 : ℝ)^1547
        have hw : |(-2215091927/10000000000 : ℝ)|=(2215091927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631878199/5000000000 : ℝ)|^2059 ≤ (5320653392443/12500000000000 : ℝ)^1547
        have hw : |(2631878199/5000000000 : ℝ)|=(2631878199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697529289/5000000000 : ℝ)|^2059 ≤ (43984207331883/100000000000000 : ℝ)^1547
        have hw : |(2697529289/5000000000 : ℝ)|=(2697529289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s6_5 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656003501/5000000000 : ℝ)*x 0 + (-1075212093/5000000000 : ℝ)*x 1 + (5395058633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656003501/5000000000 : ℝ)^2059 ≤ (2154266240117/5000000000000 : ℝ)^1547 := by
    have hnat : (2656003501 : ℕ)^2059*5000000000000^1547 ≤ 2154266240117^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656003501 5000000000 2154266240117 5000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075212093/5000000000 : ℝ)^2059 ≤ (6465233621781/50000000000000 : ℝ)^1547 := by
    have hnat : (1075212093 : ℕ)^2059*50000000000000^1547 ≤ 6465233621781^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075212093 5000000000 6465233621781 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395058633/10000000000 : ℝ)^2059 ≤ (10996051982171/25000000000000 : ℝ)^1547 := by
    have hnat : (5395058633 : ℕ)^2059*25000000000000^1547 ≤ 10996051982171^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395058633 10000000000 10996051982171 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656003501/5000000000 : ℝ), (-1075212093/5000000000 : ℝ), (5395058633/10000000000 : ℝ)] ![(2154266240117/5000000000000 : ℝ), (6465233621781/50000000000000 : ℝ), (10996051982171/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656003501/5000000000 : ℝ)|^2059 ≤ (2154266240117/5000000000000 : ℝ)^1547
        have hw : |(2656003501/5000000000 : ℝ)|=(2656003501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1075212093/5000000000 : ℝ)|^2059 ≤ (6465233621781/50000000000000 : ℝ)^1547
        have hw : |(-1075212093/5000000000 : ℝ)|=(1075212093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395058633/10000000000 : ℝ)|^2059 ≤ (10996051982171/25000000000000 : ℝ)^1547
        have hw : |(5395058633/10000000000 : ℝ)|=(5395058633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s6_6 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (664000877/1250000000 : ℝ)*x 0 + (2697529309/5000000000 : ℝ)*x 1 + (-537606047/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664000877/1250000000 : ℝ)^2059 ≤ (1723412998139/4000000000000 : ℝ)^1547 := by
    have hnat : (664000877 : ℕ)^2059*4000000000000^1547 ≤ 1723412998139^1547*1250000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664000877 1250000000 1723412998139 4000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697529309/5000000000 : ℝ)^2059 ≤ (274901298537/625000000000 : ℝ)^1547 := by
    have hnat : (2697529309 : ℕ)^2059*625000000000^1547 ≤ 274901298537^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697529309 5000000000 274901298537 625000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537606047/2500000000 : ℝ)^2059 ≤ (12930467259569/100000000000000 : ℝ)^1547 := by
    have hnat : (537606047 : ℕ)^2059*100000000000000^1547 ≤ 12930467259569^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537606047 2500000000 12930467259569 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664000877/1250000000 : ℝ), (2697529309/5000000000 : ℝ), (-537606047/2500000000 : ℝ)] ![(1723412998139/4000000000000 : ℝ), (274901298537/625000000000 : ℝ), (12930467259569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664000877/1250000000 : ℝ)|^2059 ≤ (1723412998139/4000000000000 : ℝ)^1547
        have hw : |(664000877/1250000000 : ℝ)|=(664000877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697529309/5000000000 : ℝ)|^2059 ≤ (274901298537/625000000000 : ℝ)^1547
        have hw : |(2697529309/5000000000 : ℝ)|=(2697529309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-537606047/2500000000 : ℝ)|^2059 ≤ (12930467259569/100000000000000 : ℝ)^1547
        have hw : |(-537606047/2500000000 : ℝ)|=(537606047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s6_7 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (875757811/2000000000 : ℝ)*x 0 + (563598393/1250000000 : ℝ)*x 1 + (4252627663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875757811/2000000000 : ℝ)^2059 ≤ (16658098455779/50000000000000 : ℝ)^1547 := by
    have hnat : (875757811 : ℕ)^2059*50000000000000^1547 ≤ 16658098455779^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875757811 2000000000 16658098455779 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563598393/1250000000 : ℝ)^2059 ≤ (3463907220851/10000000000000 : ℝ)^1547 := by
    have hnat : (563598393 : ℕ)^2059*10000000000000^1547 ≤ 3463907220851^1547*1250000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563598393 1250000000 3463907220851 10000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4252627663/10000000000 : ℝ)^2059 ≤ (32044730860207/100000000000000 : ℝ)^1547 := by
    have hnat : (4252627663 : ℕ)^2059*100000000000000^1547 ≤ 32044730860207^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252627663 10000000000 32044730860207 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875757811/2000000000 : ℝ), (563598393/1250000000 : ℝ), (4252627663/10000000000 : ℝ)] ![(16658098455779/50000000000000 : ℝ), (3463907220851/10000000000000 : ℝ), (32044730860207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875757811/2000000000 : ℝ)|^2059 ≤ (16658098455779/50000000000000 : ℝ)^1547
        have hw : |(875757811/2000000000 : ℝ)|=(875757811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563598393/1250000000 : ℝ)|^2059 ≤ (3463907220851/10000000000000 : ℝ)^1547
        have hw : |(563598393/1250000000 : ℝ)|=(563598393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4252627663/10000000000 : ℝ)|^2059 ≤ (32044730860207/100000000000000 : ℝ)^1547
        have hw : |(4252627663/10000000000 : ℝ)|=(4252627663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1043_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11207/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7001/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (281/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11161/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (281/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11161/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (281/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11161/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (281/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11161/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (281/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11161/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (281/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11161/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11161/100000 : ℝ) ^ (8235/2048 : ℝ) ≤ (14818966549690383/100000000000000000000 : ℝ) := by
    have hpowers : (11161/100000 : ℝ)^8235 ≤ (14818966549690383/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11161 : ℕ)^8235*100000000000000000000^2048 ≤ 14818966549690383^2048*100000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11161 100000 14818966549690383 100000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11161/100000 : ℝ)) (X := (14818966549690383/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (281/2000 : ℝ) ^ (8235/2048 : ℝ) ≤ (2337167543077623/6250000000000000000 : ℝ) := by
    have hpowers : (281/2000 : ℝ)^8235 ≤ (2337167543077623/6250000000000000000 : ℝ)^2048 := by
      have hnat : (281 : ℕ)^8235*6250000000000000000^2048 ≤ 2337167543077623^2048*2000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        281 2000 2337167543077623 6250000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (281/2000 : ℝ)) (X := (2337167543077623/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014818966549690383/50000000000000000000 : ℝ) ≤ (10000736997331491/10000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (50014818966549690383/50000000000000000000 : ℝ)^2048 ≤ (10000736997331491/10000000000000000 : ℝ)^8235 := by
      have hnat : (50014818966549690383 : ℕ)^2048*10000000000000000^8235 ≤ 10000736997331491^8235*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014818966549690383 50000000000000000000 10000736997331491 10000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000736997331491/10000000000000000 : ℝ)) (X := (50014818966549690383/50000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052213647238932351/100000000000000000000 : ℝ) ≤ (2000259654114823/2000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (100052213647238932351/100000000000000000000 : ℝ)^2048 ≤ (2000259654114823/2000000000000000 : ℝ)^8235 := by
      have hnat : (100052213647238932351 : ℕ)^2048*2000000000000000^8235 ≤ 2000259654114823^8235*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052213647238932351 100000000000000000000 2000259654114823 2000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000259654114823/2000000000000000 : ℝ)) (X := (100052213647238932351/100000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127337167543077623/3125000000000000000 : ℝ) ≤ (10001859543816739/10000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (3127337167543077623/3125000000000000000 : ℝ)^2048 ≤ (10001859543816739/10000000000000000 : ℝ)^8235 := by
      have hnat : (3127337167543077623 : ℕ)^2048*10000000000000000^8235 ≤ 10001859543816739^8235*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127337167543077623 3125000000000000000 10001859543816739 10000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001859543816739/10000000000000000 : ℝ)) (X := (3127337167543077623/3125000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14818966549690383/100000000000000000000 : ℝ) ≤ ((28879600443968824571/28890000000000000000 : ℝ)+2*(548118401/282128906250 : ℝ)*(11161/100000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (28879600443968824571/28890000000000000000 : ℝ)+2*(548118401/282128906250 : ℝ)*(11161/100000 : ℝ)=(10000736997331491/10000000000000000 : ℝ) by norm_num, show 1+2*(14818966549690383/100000000000000000000 : ℝ)=(50014818966549690383/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2337167543077623/6250000000000000000 : ℝ)+(14818966549690383/100000000000000000000 : ℝ) ≤ ((28879600443968824571/28890000000000000000 : ℝ)+(548118401/282128906250 : ℝ)*((281/2000 : ℝ)+(11161/100000 : ℝ)))^(8235/2048 : ℝ) := by
    rw [show (28879600443968824571/28890000000000000000 : ℝ)+(548118401/282128906250 : ℝ)*((281/2000 : ℝ)+(11161/100000 : ℝ))=(2000259654114823/2000000000000000 : ℝ) by norm_num, show 1+(2337167543077623/6250000000000000000 : ℝ)+(14818966549690383/100000000000000000000 : ℝ)=(100052213647238932351/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2337167543077623/6250000000000000000 : ℝ) ≤ ((28879600443968824571/28890000000000000000 : ℝ)+2*(548118401/282128906250 : ℝ)*(281/2000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (28879600443968824571/28890000000000000000 : ℝ)+2*(548118401/282128906250 : ℝ)*(281/2000 : ℝ)=(10001859543816739/10000000000000000 : ℝ) by norm_num, show 1+2*(2337167543077623/6250000000000000000 : ℝ)=(3127337167543077623/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28879600443968824571/28890000000000000000 : ℝ)*(X 1 0+X 2 0)+(548118401/282128906250 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (11161/100000 : ℝ)) (hi := (281/2000 : ℝ)) (c := (28879600443968824571/28890000000000000000 : ℝ)) (alpha := (548118401/282128906250 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28879600443968824571/28890000000000000000 : ℝ)*(X 0 1+X 2 1)+(548118401/282128906250 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (11161/100000 : ℝ)) (hi := (281/2000 : ℝ)) (c := (28879600443968824571/28890000000000000000 : ℝ)) (alpha := (548118401/282128906250 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28879600443968824571/28890000000000000000 : ℝ)*(X 0 2+X 1 2)+(548118401/282128906250 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (11161/100000 : ℝ)) (hi := (281/2000 : ℝ)) (c := (28879600443968824571/28890000000000000000 : ℝ)) (alpha := (548118401/282128906250 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-27688583/125000000 : ℝ)*X 0 0+(2697696579/5000000000 : ℝ)*X 0 1+(5263423041/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345186373/10000000000 : ℝ)*X 1 0+(-45641193/200000000 : ℝ)*X 1 1+(1315855757/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672593113/5000000000 : ℝ)*X 2 0+(5263423129/10000000000 : ℝ)*X 2 1+(-35657183/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378778719/10000000000 : ℝ)*X 0 0+(4251974839/10000000000 : ℝ)*X 0 1+(563679707/1250000000 : ℝ)*X 0 2+(4378778719/10000000000 : ℝ)*X 1 0+(4251974839/10000000000 : ℝ)*X 1 1+(563679707/1250000000 : ℝ)*X 1 2+(4378778719/10000000000 : ℝ)*X 2 0+(4251974839/10000000000 : ℝ)*X 2 1+(563679707/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2215091927/10000000000 : ℝ)*X 0 0+(2631878199/5000000000 : ℝ)*X 0 1+(2697529289/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656003501/5000000000 : ℝ)*X 1 0+(-1075212093/5000000000 : ℝ)*X 1 1+(5395058633/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664000877/1250000000 : ℝ)*X 2 0+(2697529309/5000000000 : ℝ)*X 2 1+(-537606047/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((875757811/2000000000 : ℝ)*X 0 0+(563598393/1250000000 : ℝ)*X 0 1+(4252627663/10000000000 : ℝ)*X 0 2+(875757811/2000000000 : ℝ)*X 1 0+(563598393/1250000000 : ℝ)*X 1 1+(4252627663/10000000000 : ℝ)*X 1 2+(875757811/2000000000 : ℝ)*X 2 0+(563598393/1250000000 : ℝ)*X 2 1+(4252627663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (480722997709391829925315639/240750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (253382619/50000000000000 : ℝ)*(base19) + (306393987/100000000000000 : ℝ)*(base23) + (6246641/100000000000000 : ℝ)*(upper2) + (112169567/100000000000000 : ℝ)*(upper3) + (5730785186640981/100000000000000 : ℝ)*(major0) + (5730785186640981/100000000000000 : ℝ)*(major1) + (2865392593320491/50000000000000 : ℝ)*(major2) + (1515497925692961/20000000000000 : ℝ)*(sp0) + (1894374521706857/25000000000000 : ℝ)*(sp1) + (3788748848295883/50000000000000 : ℝ)*(sp2) + (776812661597389/20000000000000 : ℝ)*(sp3) + (8965127861/100000000000000 : ℝ)*(sp4) + (295303457/50000000000000 : ℝ)*(sp6) + (1681028651/20000000000000 : ℝ)*(sp7) + (19420358565651/500000000000 : ℝ)*(f.failure) + (7577498593592667/100000000000000 : ℝ)*(f.sum) + (64529878344271/14445000000000000000000000000 : ℝ)*base65 + (19862437957198144151/2889000000000000000000000000000000 : ℝ)*base67 + (8382273171329784361/1444500000000000000000000000000000 : ℝ)*base69 + (42871436314210855849/2889000000000000000000000000000000 : ℝ)*base72 + (6123019628581/14445000000000000000000000000 : ℝ)*base73 + (30702978496645284361/1444500000000000000000000000000000 : ℝ)*base75 + (8142112173060914717/963000000000000000000000000000000 : ℝ)*base77 + (1770056477162085283/963000000000000000000000000000000 : ℝ)*base80 + (3418309446167/4815000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (169263/50000000000000000000 : ℝ)*base89 + (169263/50000000000000000000 : ℝ)*base91 + (330737/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (220254846973977787670304363/26750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1468837999/100000000000000 : ℝ)*(base19) + (794302611/50000000000000 : ℝ)*(base23) + (92147359/50000000000000 : ℝ)*(upper3) + (601129/1250000000000 : ℝ)*(lower4) + (53043829/25000000000000 : ℝ)*(upper5) + (2879959362464541/50000000000000 : ℝ)*(major0) + (2879959362464541/50000000000000 : ℝ)*(major1) + (2879959362464541/50000000000000 : ℝ)*(major2) + (20282684093/50000000000000 : ℝ)*(sp1) + (656760229/1562500000000 : ℝ)*(sp2) + (3808010021872691/50000000000000 : ℝ)*(sp4) + (7615978009539197/100000000000000 : ℝ)*(sp5) + (14874953950167/195312500000 : ℝ)*(sp6) + (60997142682061/1562500000000 : ℝ)*(sp7) + (60997142682061/1562500000000 : ℝ)*(f.failure) + (3808010021872691/50000000000000 : ℝ)*(f.sum) + (3773035197083/2407500000000000000000000000 : ℝ)*base65 + (3861756015587145637/481500000000000000000000000000000 : ℝ)*base67 + (8877911819903145637/481500000000000000000000000000000 : ℝ)*base69 + (5660774219267145637/481500000000000000000000000000000 : ℝ)*base71 + (6573369312173/2407500000000000000000000000 : ℝ)*base73 + (7813441418493645637/481500000000000000000000000000000 : ℝ)*base75 + (2733313179905145637/481500000000000000000000000000000 : ℝ)*base77 + (12235157509697145637/481500000000000000000000000000000 : ℝ)*base79 + (321352315699/75234375000000000000000000 : ℝ)*base81 + (135593/156250000000000000000 : ℝ)*base89 + (135593/156250000000000000000 : ℝ)*base91 + (135593/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1043_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1043_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1043_s7_0 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-553782959/2500000000 : ℝ)*x 0 + (2697436503/5000000000 : ℝ)*x 1 + (5263913519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (553782959/2500000000 : ℝ)^2059 ≤ (13450888062157/100000000000000 : ℝ)^1547 := by
    have hnat : (553782959 : ℕ)^2059*100000000000000^1547 ≤ 13450888062157^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553782959 2500000000 13450888062157 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697436503/5000000000 : ℝ)^2059 ≤ (1374443553627/3125000000000 : ℝ)^1547 := by
    have hnat : (2697436503 : ℕ)^2059*3125000000000^1547 ≤ 1374443553627^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697436503 5000000000 1374443553627 3125000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263913519/10000000000 : ℝ)^2059 ≤ (21283459104773/50000000000000 : ℝ)^1547 := by
    have hnat : (5263913519 : ℕ)^2059*50000000000000^1547 ≤ 21283459104773^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263913519 10000000000 21283459104773 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-553782959/2500000000 : ℝ), (2697436503/5000000000 : ℝ), (5263913519/10000000000 : ℝ)] ![(13450888062157/100000000000000 : ℝ), (1374443553627/3125000000000 : ℝ), (21283459104773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-553782959/2500000000 : ℝ)|^2059 ≤ (13450888062157/100000000000000 : ℝ)^1547
        have hw : |(-553782959/2500000000 : ℝ)|=(553782959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697436503/5000000000 : ℝ)|^2059 ≤ (1374443553627/3125000000000 : ℝ)^1547
        have hw : |(2697436503/5000000000 : ℝ)|=(2697436503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263913519/10000000000 : ℝ)|^2059 ≤ (21283459104773/50000000000000 : ℝ)^1547
        have hw : |(5263913519/10000000000 : ℝ)|=(5263913519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s7_1 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672528413/5000000000 : ℝ)*x 0 + (-71299509/312500000 : ℝ)*x 1 + (5263913717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672528413/5000000000 : ℝ)^2059 ≤ (43442476080923/100000000000000 : ℝ)^1547 := by
    have hnat : (2672528413 : ℕ)^2059*100000000000000^1547 ≤ 43442476080923^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672528413 5000000000 43442476080923 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71299509/312500000 : ℝ)^2059 ≤ (1399060356917/10000000000000 : ℝ)^1547 := by
    have hnat : (71299509 : ℕ)^2059*10000000000000^1547 ≤ 1399060356917^1547*312500000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71299509 312500000 1399060356917 10000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263913717/10000000000 : ℝ)^2059 ≤ (42566920340601/100000000000000 : ℝ)^1547 := by
    have hnat : (5263913717 : ℕ)^2059*100000000000000^1547 ≤ 42566920340601^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263913717 10000000000 42566920340601 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672528413/5000000000 : ℝ), (-71299509/312500000 : ℝ), (5263913717/10000000000 : ℝ)] ![(43442476080923/100000000000000 : ℝ), (1399060356917/10000000000000 : ℝ), (42566920340601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672528413/5000000000 : ℝ)|^2059 ≤ (43442476080923/100000000000000 : ℝ)^1547
        have hw : |(2672528413/5000000000 : ℝ)|=(2672528413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-71299509/312500000 : ℝ)|^2059 ≤ (1399060356917/10000000000000 : ℝ)^1547
        have hw : |(-71299509/312500000 : ℝ)|=(71299509/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263913717/10000000000 : ℝ)|^2059 ≤ (42566920340601/100000000000000 : ℝ)^1547
        have hw : |(5263913717/10000000000 : ℝ)|=(5263913717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s7_2 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345056909/10000000000 : ℝ)*x 0 + (2631956789/5000000000 : ℝ)*x 1 + (-57039609/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345056909/10000000000 : ℝ)^2059 ≤ (43442476978779/100000000000000 : ℝ)^1547 := by
    have hnat : (5345056909 : ℕ)^2059*100000000000000^1547 ≤ 43442476978779^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345056909 10000000000 43442476978779 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631956789/5000000000 : ℝ)^2059 ≤ (42566918844557/100000000000000 : ℝ)^1547 := by
    have hnat : (2631956789 : ℕ)^2059*100000000000000^1547 ≤ 42566918844557^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631956789 5000000000 42566918844557 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57039609/250000000 : ℝ)^2059 ≤ (13990604156793/100000000000000 : ℝ)^1547 := by
    have hnat : (57039609 : ℕ)^2059*100000000000000^1547 ≤ 13990604156793^1547*250000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57039609 250000000 13990604156793 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345056909/10000000000 : ℝ), (2631956789/5000000000 : ℝ), (-57039609/250000000 : ℝ)] ![(43442476978779/100000000000000 : ℝ), (42566918844557/100000000000000 : ℝ), (13990604156793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345056909/10000000000 : ℝ)|^2059 ≤ (43442476978779/100000000000000 : ℝ)^1547
        have hw : |(5345056909/10000000000 : ℝ)|=(5345056909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631956789/5000000000 : ℝ)|^2059 ≤ (42566918844557/100000000000000 : ℝ)^1547
        have hw : |(2631956789/5000000000 : ℝ)|=(2631956789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-57039609/250000000 : ℝ)|^2059 ≤ (13990604156793/100000000000000 : ℝ)^1547
        have hw : |(-57039609/250000000 : ℝ)|=(57039609/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s7_3 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1094701181/2500000000 : ℝ)*x 0 + (1701183/4000000 : ℝ)*x 1 + (563556013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094701181/2500000000 : ℝ)^2059 ≤ (16658177793363/50000000000000 : ℝ)^1547 := by
    have hnat : (1094701181 : ℕ)^2059*50000000000000^1547 ≤ 16658177793363^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094701181 2500000000 16658177793363 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1701183/4000000 : ℝ)^2059 ≤ (32048038896359/100000000000000 : ℝ)^1547 := by
    have hnat : (1701183 : ℕ)^2059*100000000000000^1547 ≤ 32048038896359^1547*4000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1701183 4000000 32048038896359 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563556013/1250000000 : ℝ)^2059 ≤ (17317802746969/50000000000000 : ℝ)^1547 := by
    have hnat : (563556013 : ℕ)^2059*50000000000000^1547 ≤ 17317802746969^1547*1250000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563556013 1250000000 17317802746969 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094701181/2500000000 : ℝ), (1701183/4000000 : ℝ), (563556013/1250000000 : ℝ)] ![(16658177793363/50000000000000 : ℝ), (32048038896359/100000000000000 : ℝ), (17317802746969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094701181/2500000000 : ℝ)|^2059 ≤ (16658177793363/50000000000000 : ℝ)^1547
        have hw : |(1094701181/2500000000 : ℝ)|=(1094701181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1701183/4000000 : ℝ)|^2059 ≤ (32048038896359/100000000000000 : ℝ)^1547
        have hw : |(1701183/4000000 : ℝ)|=(1701183/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563556013/1250000000 : ℝ)|^2059 ≤ (17317802746969/50000000000000 : ℝ)^1547
        have hw : |(563556013/1250000000 : ℝ)|=(563556013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s7_4 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-553784219/2500000000 : ℝ)*x 0 + (5264241959/10000000000 : ℝ)*x 1 + (1078908693/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (553784219/2500000000 : ℝ)^2059 ≤ (6725464397659/50000000000000 : ℝ)^1547 := by
    have hnat : (553784219 : ℕ)^2059*50000000000000^1547 ≤ 6725464397659^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553784219 2500000000 6725464397659 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264241959/10000000000 : ℝ)^2059 ≤ (1702818128579/4000000000000 : ℝ)^1547 := by
    have hnat : (5264241959 : ℕ)^2059*4000000000000^1547 ≤ 1702818128579^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264241959 10000000000 1702818128579 4000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078908693/2000000000 : ℝ)^2059 ≤ (43978617969259/100000000000000 : ℝ)^1547 := by
    have hnat : (1078908693 : ℕ)^2059*100000000000000^1547 ≤ 43978617969259^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078908693 2000000000 43978617969259 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-553784219/2500000000 : ℝ), (5264241959/10000000000 : ℝ), (1078908693/2000000000 : ℝ)] ![(6725464397659/50000000000000 : ℝ), (1702818128579/4000000000000 : ℝ), (43978617969259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-553784219/2500000000 : ℝ)|^2059 ≤ (6725464397659/50000000000000 : ℝ)^1547
        have hw : |(-553784219/2500000000 : ℝ)|=(553784219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264241959/10000000000 : ℝ)|^2059 ≤ (1702818128579/4000000000000 : ℝ)^1547
        have hw : |(5264241959/10000000000 : ℝ)|=(5264241959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078908693/2000000000 : ℝ)|^2059 ≤ (43978617969259/100000000000000 : ℝ)^1547
        have hw : |(1078908693/2000000000 : ℝ)|=(1078908693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s7_5 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656065819/5000000000 : ℝ)*x 0 + (-53773863/250000000 : ℝ)*x 1 + (2697271733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656065819/5000000000 : ℝ)^2059 ≤ (10771667574231/25000000000000 : ℝ)^1547 := by
    have hnat : (2656065819 : ℕ)^2059*25000000000000^1547 ≤ 10771667574231^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656065819 5000000000 10771667574231 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53773863/250000000 : ℝ)^2059 ≤ (3233677928001/25000000000000 : ℝ)^1547 := by
    have hnat : (53773863 : ℕ)^2059*25000000000000^1547 ≤ 3233677928001^1547*250000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53773863 250000000 3233677928001 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697271733/5000000000 : ℝ)^2059 ≤ (4397861798011/10000000000000 : ℝ)^1547 := by
    have hnat : (2697271733 : ℕ)^2059*10000000000000^1547 ≤ 4397861798011^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697271733 5000000000 4397861798011 10000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656065819/5000000000 : ℝ), (-53773863/250000000 : ℝ), (2697271733/5000000000 : ℝ)] ![(10771667574231/25000000000000 : ℝ), (3233677928001/25000000000000 : ℝ), (4397861798011/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656065819/5000000000 : ℝ)|^2059 ≤ (10771667574231/25000000000000 : ℝ)^1547
        have hw : |(2656065819/5000000000 : ℝ)|=(2656065819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-53773863/250000000 : ℝ)|^2059 ≤ (3233677928001/25000000000000 : ℝ)^1547
        have hw : |(-53773863/250000000 : ℝ)|=(53773863/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697271733/5000000000 : ℝ)|^2059 ≤ (4397861798011/10000000000000 : ℝ)^1547
        have hw : |(2697271733/5000000000 : ℝ)|=(2697271733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s7_6 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656065819/5000000000 : ℝ)*x 0 + (1078908693/2000000000 : ℝ)*x 1 + (-53773863/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656065819/5000000000 : ℝ)^2059 ≤ (10771667574231/25000000000000 : ℝ)^1547 := by
    have hnat : (2656065819 : ℕ)^2059*25000000000000^1547 ≤ 10771667574231^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656065819 5000000000 10771667574231 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078908693/2000000000 : ℝ)^2059 ≤ (43978617969259/100000000000000 : ℝ)^1547 := by
    have hnat : (1078908693 : ℕ)^2059*100000000000000^1547 ≤ 43978617969259^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078908693 2000000000 43978617969259 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53773863/250000000 : ℝ)^2059 ≤ (3233677928001/25000000000000 : ℝ)^1547 := by
    have hnat : (53773863 : ℕ)^2059*25000000000000^1547 ≤ 3233677928001^1547*250000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53773863 250000000 3233677928001 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656065819/5000000000 : ℝ), (1078908693/2000000000 : ℝ), (-53773863/250000000 : ℝ)] ![(10771667574231/25000000000000 : ℝ), (43978617969259/100000000000000 : ℝ), (3233677928001/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656065819/5000000000 : ℝ)|^2059 ≤ (10771667574231/25000000000000 : ℝ)^1547
        have hw : |(2656065819/5000000000 : ℝ)|=(2656065819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078908693/2000000000 : ℝ)|^2059 ≤ (43978617969259/100000000000000 : ℝ)^1547
        have hw : |(1078908693/2000000000 : ℝ)|=(1078908693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-53773863/250000000 : ℝ)|^2059 ≤ (3233677928001/25000000000000 : ℝ)^1547
        have hw : |(-53773863/250000000 : ℝ)|=(53773863/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s7_7 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2189407361/5000000000 : ℝ)*x 0 + (2253903823/5000000000 : ℝ)*x 1 + (4253600319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189407361/5000000000 : ℝ)^2059 ≤ (33316456833511/100000000000000 : ℝ)^1547 := by
    have hnat : (2189407361 : ℕ)^2059*100000000000000^1547 ≤ 33316456833511^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189407361 5000000000 33316456833511 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253903823/5000000000 : ℝ)^2059 ≤ (17314528494289/50000000000000 : ℝ)^1547 := by
    have hnat : (2253903823 : ℕ)^2059*50000000000000^1547 ≤ 17314528494289^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253903823 5000000000 17314528494289 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4253600319/10000000000 : ℝ)^2059 ≤ (250425673193/781250000000 : ℝ)^1547 := by
    have hnat : (4253600319 : ℕ)^2059*781250000000^1547 ≤ 250425673193^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253600319 10000000000 250425673193 781250000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189407361/5000000000 : ℝ), (2253903823/5000000000 : ℝ), (4253600319/10000000000 : ℝ)] ![(33316456833511/100000000000000 : ℝ), (17314528494289/50000000000000 : ℝ), (250425673193/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189407361/5000000000 : ℝ)|^2059 ≤ (33316456833511/100000000000000 : ℝ)^1547
        have hw : |(2189407361/5000000000 : ℝ)|=(2189407361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253903823/5000000000 : ℝ)|^2059 ≤ (17314528494289/50000000000000 : ℝ)^1547
        have hw : |(2253903823/5000000000 : ℝ)|=(2253903823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4253600319/10000000000 : ℝ)|^2059 ≤ (250425673193/781250000000 : ℝ)^1547
        have hw : |(4253600319/10000000000 : ℝ)|=(4253600319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1043_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11217/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13991/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7001/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7001/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7001/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7001/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7001/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7001/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11207/100000 : ℝ) ^ (8235/2048 : ℝ) ≤ (15066087225987047/100000000000000000000 : ℝ) := by
    have hpowers : (11207/100000 : ℝ)^8235 ≤ (15066087225987047/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11207 : ℕ)^8235*100000000000000000000^2048 ≤ 15066087225987047^2048*100000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11207 100000 15066087225987047 100000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11207/100000 : ℝ)) (X := (15066087225987047/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7001/50000 : ℝ) ^ (8235/2048 : ℝ) ≤ (368836268808811/1000000000000000000 : ℝ) := by
    have hpowers : (7001/50000 : ℝ)^8235 ≤ (368836268808811/1000000000000000000 : ℝ)^2048 := by
      have hnat : (7001 : ℕ)^8235*1000000000000000000^2048 ≤ 368836268808811^2048*50000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7001 50000 368836268808811 1000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7001/50000 : ℝ)) (X := (368836268808811/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015066087225987047/50000000000000000000 : ℝ) ≤ (2000149857217557/2000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (50015066087225987047/50000000000000000000 : ℝ)^2048 ≤ (2000149857217557/2000000000000000 : ℝ)^8235 := by
      have hnat : (50015066087225987047 : ℕ)^2048*2000000000000000^8235 ≤ 2000149857217557^8235*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015066087225987047 50000000000000000000 2000149857217557 2000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000149857217557/2000000000000000 : ℝ)) (X := (50015066087225987047/50000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051949714106868147/100000000000000000000 : ℝ) ≤ (1250161463658371/1250000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (100051949714106868147/100000000000000000000 : ℝ)^2048 ≤ (1250161463658371/1250000000000000 : ℝ)^8235 := by
      have hnat : (100051949714106868147 : ℕ)^2048*1250000000000000^8235 ≤ 1250161463658371^8235*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051949714106868147 100000000000000000000 1250161463658371 1250000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250161463658371/1250000000000000 : ℝ)) (X := (100051949714106868147/100000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (500368836268808811/500000000000000000 : ℝ) ≤ (10001834132446151/10000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (500368836268808811/500000000000000000 : ℝ)^2048 ≤ (10001834132446151/10000000000000000 : ℝ)^8235 := by
      have hnat : (500368836268808811 : ℕ)^2048*10000000000000000^8235 ≤ 10001834132446151^8235*500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500368836268808811 500000000000000000 10001834132446151 10000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001834132446151/10000000000000000 : ℝ)) (X := (500368836268808811/500000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15066087225987047/100000000000000000000 : ℝ) ≤ ((27939936381477151313/27950000000000000000 : ℝ)+2*(542423179183/279500000000000 : ℝ)*(11207/100000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (27939936381477151313/27950000000000000000 : ℝ)+2*(542423179183/279500000000000 : ℝ)*(11207/100000 : ℝ)=(2000149857217557/2000000000000000 : ℝ) by norm_num, show 1+2*(15066087225987047/100000000000000000000 : ℝ)=(50015066087225987047/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(368836268808811/1000000000000000000 : ℝ)+(15066087225987047/100000000000000000000 : ℝ) ≤ ((27939936381477151313/27950000000000000000 : ℝ)+(542423179183/279500000000000 : ℝ)*((7001/50000 : ℝ)+(11207/100000 : ℝ)))^(8235/2048 : ℝ) := by
    rw [show (27939936381477151313/27950000000000000000 : ℝ)+(542423179183/279500000000000 : ℝ)*((7001/50000 : ℝ)+(11207/100000 : ℝ))=(1250161463658371/1250000000000000 : ℝ) by norm_num, show 1+(368836268808811/1000000000000000000 : ℝ)+(15066087225987047/100000000000000000000 : ℝ)=(100051949714106868147/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(368836268808811/1000000000000000000 : ℝ) ≤ ((27939936381477151313/27950000000000000000 : ℝ)+2*(542423179183/279500000000000 : ℝ)*(7001/50000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (27939936381477151313/27950000000000000000 : ℝ)+2*(542423179183/279500000000000 : ℝ)*(7001/50000 : ℝ)=(10001834132446151/10000000000000000 : ℝ) by norm_num, show 1+2*(368836268808811/1000000000000000000 : ℝ)=(500368836268808811/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27939936381477151313/27950000000000000000 : ℝ)*(X 1 0+X 2 0)+(542423179183/279500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (7001/50000 : ℝ)) (c := (27939936381477151313/27950000000000000000 : ℝ)) (alpha := (542423179183/279500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27939936381477151313/27950000000000000000 : ℝ)*(X 0 1+X 2 1)+(542423179183/279500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (7001/50000 : ℝ)) (c := (27939936381477151313/27950000000000000000 : ℝ)) (alpha := (542423179183/279500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27939936381477151313/27950000000000000000 : ℝ)*(X 0 2+X 1 2)+(542423179183/279500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (7001/50000 : ℝ)) (c := (27939936381477151313/27950000000000000000 : ℝ)) (alpha := (542423179183/279500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-553782959/2500000000 : ℝ)*X 0 0+(2697436503/5000000000 : ℝ)*X 0 1+(5263913519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672528413/5000000000 : ℝ)*X 1 0+(-71299509/312500000 : ℝ)*X 1 1+(5263913717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345056909/10000000000 : ℝ)*X 2 0+(2631956789/5000000000 : ℝ)*X 2 1+(-57039609/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1094701181/2500000000 : ℝ)*X 0 0+(1701183/4000000 : ℝ)*X 0 1+(563556013/1250000000 : ℝ)*X 0 2+(1094701181/2500000000 : ℝ)*X 1 0+(1701183/4000000 : ℝ)*X 1 1+(563556013/1250000000 : ℝ)*X 1 2+(1094701181/2500000000 : ℝ)*X 2 0+(1701183/4000000 : ℝ)*X 2 1+(563556013/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-553784219/2500000000 : ℝ)*X 0 0+(5264241959/10000000000 : ℝ)*X 0 1+(1078908693/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656065819/5000000000 : ℝ)*X 1 0+(-53773863/250000000 : ℝ)*X 1 1+(2697271733/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656065819/5000000000 : ℝ)*X 2 0+(1078908693/2000000000 : ℝ)*X 2 1+(-53773863/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2189407361/5000000000 : ℝ)*X 0 0+(2253903823/5000000000 : ℝ)*X 0 1+(4253600319/10000000000 : ℝ)*X 0 2+(2189407361/5000000000 : ℝ)*X 1 0+(2253903823/5000000000 : ℝ)*X 1 1+(4253600319/10000000000 : ℝ)*X 1 2+(2189407361/5000000000 : ℝ)*X 2 0+(2253903823/5000000000 : ℝ)*X 2 1+(4253600319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3849554653874040341880154227/698750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (168144189/12500000000000 : ℝ)*(base19) + (1419821541/100000000000000 : ℝ)*(base23) + (113102401/50000000000000 : ℝ)*(upper3) + (23468627/100000000000000 : ℝ)*(upper4) + (103603399/100000000000000 : ℝ)*(upper5) + (5775058843792387/100000000000000 : ℝ)*(major0) + (5775058843792387/100000000000000 : ℝ)*(major1) + (1443764710948097/25000000000000 : ℝ)*(major2) + (763599604477639/10000000000000 : ℝ)*(sp0) + (7636037726899411/100000000000000 : ℝ)*(sp1) + (7636037652231383/100000000000000 : ℝ)*(sp2) + (3914056636142861/100000000000000 : ℝ)*(sp3) + (21513638267/50000000000000 : ℝ)*(sp4) + (871829957/4000000000000 : ℝ)*(sp7) + (1957039215945893/50000000000000 : ℝ)*(f.failure) + (1909009768013231/25000000000000 : ℝ)*(f.sum) + (240678527041/86000000000000000000000000 : ℝ)*base65 + (663279864063145869/2795000000000000000000000000000000 : ℝ)*base68 + (4744603500827676361/698750000000000000000000000000000 : ℝ)*base69 + (32425582174243145869/2795000000000000000000000000000000 : ℝ)*base72 + (76687642071/86000000000000000000000000 : ℝ)*base74 + (6455455166386426361/698750000000000000000000000000000 : ℝ)*base75 + (39159443114656445869/2795000000000000000000000000000000 : ℝ)*base78 + (38381264980741445869/2795000000000000000000000000000000 : ℝ)*base80 + (12139012125287/1746875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3303991/5000000000000000000000 : ℝ)*base90 + (3303991/5000000000000000000000 : ℝ)*base92 + (53303991/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (100927882536366246666087/13975000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1350271839/100000000000000 : ℝ)*(base19) + (1468613667/100000000000000 : ℝ)*(base23) + (18144077/12500000000000 : ℝ)*(upper3) + (26956653/50000000000000 : ℝ)*(lower4) + (147617501/100000000000000 : ℝ)*(upper5) + (2902075960263269/50000000000000 : ℝ)*(major0) + (2902075960263269/50000000000000 : ℝ)*(major1) + (2902075960263269/50000000000000 : ℝ)*(major2) + (18275954051/50000000000000 : ℝ)*(sp1) + (981763183/2500000000000 : ℝ)*(sp2) + (1918626793237427/25000000000000 : ℝ)*(sp4) + (959308658846221/12500000000000 : ℝ)*(sp5) + (3837233216904361/50000000000000 : ℝ)*(sp6) + (786759285473799/20000000000000 : ℝ)*(sp7) + (786759285473799/20000000000000 : ℝ)*(f.failure) + (1918626793237427/25000000000000 : ℝ)*(f.sum) + (2224396771249/3493750000000000000000000000 : ℝ)*base66 + (253699527893277803/1397500000000000000000000000000000 : ℝ)*base68 + (17060998620614222197/1397500000000000000000000000000000 : ℝ)*base69 + (3788799971716722197/1397500000000000000000000000000000 : ℝ)*base71 + (111548824089/218359375000000000000000000 : ℝ)*base74 + (32313952020180777803/1397500000000000000000000000000000 : ℝ)*base76 + (4223036370416722197/1397500000000000000000000000000000 : ℝ)*base77 + (12331809496298277803/1397500000000000000000000000000000 : ℝ)*base80 + (93838806717579/13975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3653587/2000000000000000000000 : ℝ)*base89 + (3653587/2000000000000000000000 : ℝ)*base91 + (3653587/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1043_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11217/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13991/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1043_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1043_s8_0 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1107571779/5000000000 : ℝ)*x 0 + (269737887/500000000 : ℝ)*x 1 + (5264020923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107571779/5000000000 : ℝ)^2059 ≤ (13450982799131/100000000000000 : ℝ)^1547 := by
    have hnat : (1107571779 : ℕ)^2059*100000000000000^1547 ≤ 13450982799131^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107571779 5000000000 13450982799131 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269737887/500000000 : ℝ)^2059 ≤ (43980942992359/100000000000000 : ℝ)^1547 := by
    have hnat : (269737887 : ℕ)^2059*100000000000000^1547 ≤ 43980942992359^1547*500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269737887 500000000 43980942992359 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264020923/10000000000 : ℝ)^2059 ≤ (42568074192469/100000000000000 : ℝ)^1547 := by
    have hnat : (5264020923 : ℕ)^2059*100000000000000^1547 ≤ 42568074192469^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264020923 10000000000 42568074192469 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1107571779/5000000000 : ℝ), (269737887/500000000 : ℝ), (5264020923/10000000000 : ℝ)] ![(13450982799131/100000000000000 : ℝ), (43980942992359/100000000000000 : ℝ), (42568074192469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1107571779/5000000000 : ℝ)|^2059 ≤ (13450982799131/100000000000000 : ℝ)^1547
        have hw : |(-1107571779/5000000000 : ℝ)|=(1107571779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269737887/500000000 : ℝ)|^2059 ≤ (43980942992359/100000000000000 : ℝ)^1547
        have hw : |(269737887/500000000 : ℝ)|=(269737887/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264020923/10000000000 : ℝ)|^2059 ≤ (42568074192469/100000000000000 : ℝ)^1547
        have hw : |(5264020923/10000000000 : ℝ)|=(5264020923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s8_1 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167032113/312500000 : ℝ)*x 0 + (-1140740813/5000000000 : ℝ)*x 1 + (2632010461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167032113/312500000 : ℝ)^2059 ≤ (8688432020207/20000000000000 : ℝ)^1547 := by
    have hnat : (167032113 : ℕ)^2059*20000000000000^1547 ≤ 8688432020207^1547*312500000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167032113 312500000 8688432020207 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140740813/5000000000 : ℝ)^2059 ≤ (13989765707249/100000000000000 : ℝ)^1547 := by
    have hnat : (1140740813 : ℕ)^2059*100000000000000^1547 ≤ 13989765707249^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140740813 5000000000 13989765707249 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632010461/5000000000 : ℝ)^2059 ≤ (21284037090853/50000000000000 : ℝ)^1547 := by
    have hnat : (2632010461 : ℕ)^2059*50000000000000^1547 ≤ 21284037090853^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632010461 5000000000 21284037090853 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167032113/312500000 : ℝ), (-1140740813/5000000000 : ℝ), (2632010461/5000000000 : ℝ)] ![(8688432020207/20000000000000 : ℝ), (13989765707249/100000000000000 : ℝ), (21284037090853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167032113/312500000 : ℝ)|^2059 ≤ (8688432020207/20000000000000 : ℝ)^1547
        have hw : |(167032113/312500000 : ℝ)|=(167032113/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1140740813/5000000000 : ℝ)|^2059 ≤ (13989765707249/100000000000000 : ℝ)^1547
        have hw : |(-1140740813/5000000000 : ℝ)|=(1140740813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632010461/5000000000 : ℝ)|^2059 ≤ (21284037090853/50000000000000 : ℝ)^1547
        have hw : |(2632010461/5000000000 : ℝ)|=(2632010461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s8_2 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345027613/10000000000 : ℝ)*x 0 + (5264020931/10000000000 : ℝ)*x 1 + (-1140740809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345027613/10000000000 : ℝ)^2059 ≤ (43442160068583/100000000000000 : ℝ)^1547 := by
    have hnat : (5345027613 : ℕ)^2059*100000000000000^1547 ≤ 43442160068583^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345027613 10000000000 43442160068583 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264020931/10000000000 : ℝ)^2059 ≤ (42568074278573/100000000000000 : ℝ)^1547 := by
    have hnat : (5264020931 : ℕ)^2059*100000000000000^1547 ≤ 42568074278573^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264020931 10000000000 42568074278573 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140740809/5000000000 : ℝ)^2059 ≤ (6994882820979/50000000000000 : ℝ)^1547 := by
    have hnat : (1140740809 : ℕ)^2059*50000000000000^1547 ≤ 6994882820979^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140740809 5000000000 6994882820979 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345027613/10000000000 : ℝ), (5264020931/10000000000 : ℝ), (-1140740809/5000000000 : ℝ)] ![(43442160068583/100000000000000 : ℝ), (42568074278573/100000000000000 : ℝ), (6994882820979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345027613/10000000000 : ℝ)|^2059 ≤ (43442160068583/100000000000000 : ℝ)^1547
        have hw : |(5345027613/10000000000 : ℝ)|=(5345027613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264020931/10000000000 : ℝ)|^2059 ≤ (42568074278573/100000000000000 : ℝ)^1547
        have hw : |(5264020931/10000000000 : ℝ)|=(5264020931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1140740809/5000000000 : ℝ)|^2059 ≤ (6994882820979/50000000000000 : ℝ)^1547
        have hw : |(-1140740809/5000000000 : ℝ)|=(1140740809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s8_3 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4378810369/10000000000 : ℝ)*x 0 + (850634757/2000000000 : ℝ)*x 1 + (4508230361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378810369/10000000000 : ℝ)^2059 ≤ (832910318799/2500000000000 : ℝ)^1547 := by
    have hnat : (4378810369 : ℕ)^2059*2500000000000^1547 ≤ 832910318799^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378810369 10000000000 832910318799 2500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (850634757/2000000000 : ℝ)^2059 ≤ (8012552032717/25000000000000 : ℝ)^1547 := by
    have hnat : (850634757 : ℕ)^2059*25000000000000^1547 ≤ 8012552032717^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850634757 2000000000 8012552032717 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508230361/10000000000 : ℝ)^2059 ≤ (8658344774407/25000000000000 : ℝ)^1547 := by
    have hnat : (4508230361 : ℕ)^2059*25000000000000^1547 ≤ 8658344774407^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508230361 10000000000 8658344774407 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378810369/10000000000 : ℝ), (850634757/2000000000 : ℝ), (4508230361/10000000000 : ℝ)] ![(832910318799/2500000000000 : ℝ), (8012552032717/25000000000000 : ℝ), (8658344774407/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378810369/10000000000 : ℝ)|^2059 ≤ (832910318799/2500000000000 : ℝ)^1547
        have hw : |(4378810369/10000000000 : ℝ)|=(4378810369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(850634757/2000000000 : ℝ)|^2059 ≤ (8012552032717/25000000000000 : ℝ)^1547
        have hw : |(850634757/2000000000 : ℝ)|=(850634757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508230361/10000000000 : ℝ)|^2059 ≤ (8658344774407/25000000000000 : ℝ)^1547
        have hw : |(4508230361/10000000000 : ℝ)|=(4508230361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s8_4 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2215148667/10000000000 : ℝ)*x 0 + (2632174059/5000000000 : ℝ)*x 1 + (5394429379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2215148667/10000000000 : ℝ)^2059 ≤ (13451024090021/100000000000000 : ℝ)^1547 := by
    have hnat : (2215148667 : ℕ)^2059*100000000000000^1547 ≤ 13451024090021^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215148667 10000000000 13451024090021 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632174059/5000000000 : ℝ)^2059 ≤ (21285797910543/50000000000000 : ℝ)^1547 := by
    have hnat : (2632174059 : ℕ)^2059*50000000000000^1547 ≤ 21285797910543^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632174059 5000000000 21285797910543 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394429379/10000000000 : ℝ)^2059 ≤ (21988690037217/50000000000000 : ℝ)^1547 := by
    have hnat : (5394429379 : ℕ)^2059*50000000000000^1547 ≤ 21988690037217^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394429379 10000000000 21988690037217 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2215148667/10000000000 : ℝ), (2632174059/5000000000 : ℝ), (5394429379/10000000000 : ℝ)] ![(13451024090021/100000000000000 : ℝ), (21285797910543/50000000000000 : ℝ), (21988690037217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2215148667/10000000000 : ℝ)|^2059 ≤ (13451024090021/100000000000000 : ℝ)^1547
        have hw : |(-2215148667/10000000000 : ℝ)|=(2215148667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632174059/5000000000 : ℝ)|^2059 ≤ (21285797910543/50000000000000 : ℝ)^1547
        have hw : |(2632174059/5000000000 : ℝ)|=(2632174059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394429379/10000000000 : ℝ)|^2059 ≤ (21988690037217/50000000000000 : ℝ)^1547
        have hw : |(5394429379/10000000000 : ℝ)|=(5394429379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s8_5 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656079223/5000000000 : ℝ)*x 0 + (-2151073089/10000000000 : ℝ)*x 1 + (5394429333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656079223/5000000000 : ℝ)^2059 ≤ (43086959701181/100000000000000 : ℝ)^1547 := by
    have hnat : (2656079223 : ℕ)^2059*100000000000000^1547 ≤ 43086959701181^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656079223 5000000000 43086959701181 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2151073089/10000000000 : ℝ)^2059 ≤ (646783035651/5000000000000 : ℝ)^1547 := by
    have hnat : (2151073089 : ℕ)^2059*5000000000000^1547 ≤ 646783035651^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151073089 10000000000 646783035651 5000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394429333/10000000000 : ℝ)^2059 ≤ (43977379575311/100000000000000 : ℝ)^1547 := by
    have hnat : (5394429333 : ℕ)^2059*100000000000000^1547 ≤ 43977379575311^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394429333 10000000000 43977379575311 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656079223/5000000000 : ℝ), (-2151073089/10000000000 : ℝ), (5394429333/10000000000 : ℝ)] ![(43086959701181/100000000000000 : ℝ), (646783035651/5000000000000 : ℝ), (43977379575311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656079223/5000000000 : ℝ)|^2059 ≤ (43086959701181/100000000000000 : ℝ)^1547
        have hw : |(2656079223/5000000000 : ℝ)|=(2656079223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2151073089/10000000000 : ℝ)|^2059 ≤ (646783035651/5000000000000 : ℝ)^1547
        have hw : |(-2151073089/10000000000 : ℝ)|=(2151073089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394429333/10000000000 : ℝ)|^2059 ≤ (43977379575311/100000000000000 : ℝ)^1547
        have hw : |(5394429333/10000000000 : ℝ)|=(5394429333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s8_6 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062431643/2000000000 : ℝ)*x 0 + (5394429283/10000000000 : ℝ)*x 1 + (-537768367/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062431643/2000000000 : ℝ)^2059 ≤ (5385869650929/12500000000000 : ℝ)^1547 := by
    have hnat : (1062431643 : ℕ)^2059*12500000000000^1547 ≤ 5385869650929^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062431643 2000000000 5385869650929 12500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394429283/10000000000 : ℝ)^2059 ≤ (21988689516393/50000000000000 : ℝ)^1547 := by
    have hnat : (5394429283 : ℕ)^2059*50000000000000^1547 ≤ 21988689516393^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394429283 10000000000 21988689516393 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537768367/2500000000 : ℝ)^2059 ≤ (12935663746483/100000000000000 : ℝ)^1547 := by
    have hnat : (537768367 : ℕ)^2059*100000000000000^1547 ≤ 12935663746483^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537768367 2500000000 12935663746483 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062431643/2000000000 : ℝ), (5394429283/10000000000 : ℝ), (-537768367/2500000000 : ℝ)] ![(5385869650929/12500000000000 : ℝ), (21988689516393/50000000000000 : ℝ), (12935663746483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062431643/2000000000 : ℝ)|^2059 ≤ (5385869650929/12500000000000 : ℝ)^1547
        have hw : |(1062431643/2000000000 : ℝ)|=(1062431643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394429283/10000000000 : ℝ)|^2059 ≤ (21988689516393/50000000000000 : ℝ)^1547
        have hw : |(5394429283/10000000000 : ℝ)|=(5394429283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-537768367/2500000000 : ℝ)|^2059 ≤ (12935663746483/100000000000000 : ℝ)^1547
        have hw : |(-537768367/2500000000 : ℝ)|=(537768367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s8_7 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4378819989/10000000000 : ℝ)*x 0 + (901518413/2000000000 : ℝ)*x 1 + (106345369/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378819989/10000000000 : ℝ)^2059 ≤ (33316510170891/100000000000000 : ℝ)^1547 := by
    have hnat : (4378819989 : ℕ)^2059*100000000000000^1547 ≤ 33316510170891^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378819989 10000000000 33316510170891 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901518413/2000000000 : ℝ)^2059 ≤ (3462685280193/10000000000000 : ℝ)^1547 := by
    have hnat : (901518413 : ℕ)^2059*10000000000000^1547 ≤ 3462685280193^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901518413 2000000000 3462685280193 10000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106345369/250000000 : ℝ)^2059 ≤ (32056637016207/100000000000000 : ℝ)^1547 := by
    have hnat : (106345369 : ℕ)^2059*100000000000000^1547 ≤ 32056637016207^1547*250000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106345369 250000000 32056637016207 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378819989/10000000000 : ℝ), (901518413/2000000000 : ℝ), (106345369/250000000 : ℝ)] ![(33316510170891/100000000000000 : ℝ), (3462685280193/10000000000000 : ℝ), (32056637016207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378819989/10000000000 : ℝ)|^2059 ≤ (33316510170891/100000000000000 : ℝ)^1547
        have hw : |(4378819989/10000000000 : ℝ)|=(4378819989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901518413/2000000000 : ℝ)|^2059 ≤ (3462685280193/10000000000000 : ℝ)^1547
        have hw : |(901518413/2000000000 : ℝ)|=(901518413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(106345369/250000000 : ℝ)|^2059 ≤ (32056637016207/100000000000000 : ℝ)^1547
        have hw : |(106345369/250000000 : ℝ)|=(106345369/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1043_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13991/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11219/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13989/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13991/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11217/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13991/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11217/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13991/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11217/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13991/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11217/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13991/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11217/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13991/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11217/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11217/100000 : ℝ) ^ (8235/2048 : ℝ) ≤ (15120216233410153/100000000000000000000 : ℝ) := by
    have hpowers : (11217/100000 : ℝ)^8235 ≤ (15120216233410153/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11217 : ℕ)^8235*100000000000000000000^2048 ≤ 15120216233410153^2048*100000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11217 100000 15120216233410153 100000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11217/100000 : ℝ)) (X := (15120216233410153/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13991/100000 : ℝ) ^ (8235/2048 : ℝ) ≤ (18383626637095339/50000000000000000000 : ℝ) := by
    have hpowers : (13991/100000 : ℝ)^8235 ≤ (18383626637095339/50000000000000000000 : ℝ)^2048 := by
      have hnat : (13991 : ℕ)^8235*50000000000000000000^2048 ≤ 18383626637095339^2048*100000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13991 100000 18383626637095339 50000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13991/100000 : ℝ)) (X := (18383626637095339/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015120216233410153/50000000000000000000 : ℝ) ≤ (5000375988897841/5000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (50015120216233410153/50000000000000000000 : ℝ)^2048 ≤ (5000375988897841/5000000000000000 : ℝ)^8235 := by
      have hnat : (50015120216233410153 : ℕ)^2048*5000000000000000^8235 ≤ 5000375988897841^8235*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015120216233410153 50000000000000000000 5000375988897841 5000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000375988897841/5000000000000000 : ℝ)) (X := (50015120216233410153/50000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051887469507600831/100000000000000000000 : ℝ) ≤ (2000258032376193/2000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (100051887469507600831/100000000000000000000 : ℝ)^2048 ≤ (2000258032376193/2000000000000000 : ℝ)^8235 := by
      have hnat : (100051887469507600831 : ℕ)^2048*2000000000000000^8235 ≤ 2000258032376193^8235*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051887469507600831 100000000000000000000 2000258032376193 2000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000258032376193/2000000000000000 : ℝ)) (X := (100051887469507600831/100000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018383626637095339/25000000000000000000 : ℝ) ≤ (1250228543245781/1250000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (25018383626637095339/25000000000000000000 : ℝ)^2048 ≤ (1250228543245781/1250000000000000 : ℝ)^8235 := by
      have hnat : (25018383626637095339 : ℕ)^2048*1250000000000000^8235 ≤ 1250228543245781^8235*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018383626637095339 25000000000000000000 1250228543245781 1250000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250228543245781/1250000000000000 : ℝ)) (X := (25018383626637095339/25000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15120216233410153/100000000000000000000 : ℝ) ≤ ((13865006182317991523/13870000000000000000 : ℝ)+2*(538184085283/277400000000000 : ℝ)*(11217/100000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (13865006182317991523/13870000000000000000 : ℝ)+2*(538184085283/277400000000000 : ℝ)*(11217/100000 : ℝ)=(5000375988897841/5000000000000000 : ℝ) by norm_num, show 1+2*(15120216233410153/100000000000000000000 : ℝ)=(50015120216233410153/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18383626637095339/50000000000000000000 : ℝ)+(15120216233410153/100000000000000000000 : ℝ) ≤ ((13865006182317991523/13870000000000000000 : ℝ)+(538184085283/277400000000000 : ℝ)*((13991/100000 : ℝ)+(11217/100000 : ℝ)))^(8235/2048 : ℝ) := by
    rw [show (13865006182317991523/13870000000000000000 : ℝ)+(538184085283/277400000000000 : ℝ)*((13991/100000 : ℝ)+(11217/100000 : ℝ))=(2000258032376193/2000000000000000 : ℝ) by norm_num, show 1+(18383626637095339/50000000000000000000 : ℝ)+(15120216233410153/100000000000000000000 : ℝ)=(100051887469507600831/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18383626637095339/50000000000000000000 : ℝ) ≤ ((13865006182317991523/13870000000000000000 : ℝ)+2*(538184085283/277400000000000 : ℝ)*(13991/100000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (13865006182317991523/13870000000000000000 : ℝ)+2*(538184085283/277400000000000 : ℝ)*(13991/100000 : ℝ)=(1250228543245781/1250000000000000 : ℝ) by norm_num, show 1+2*(18383626637095339/50000000000000000000 : ℝ)=(25018383626637095339/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13865006182317991523/13870000000000000000 : ℝ)*(X 1 0+X 2 0)+(538184085283/277400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (11217/100000 : ℝ)) (hi := (13991/100000 : ℝ)) (c := (13865006182317991523/13870000000000000000 : ℝ)) (alpha := (538184085283/277400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13865006182317991523/13870000000000000000 : ℝ)*(X 0 1+X 2 1)+(538184085283/277400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (11217/100000 : ℝ)) (hi := (13991/100000 : ℝ)) (c := (13865006182317991523/13870000000000000000 : ℝ)) (alpha := (538184085283/277400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13865006182317991523/13870000000000000000 : ℝ)*(X 0 2+X 1 2)+(538184085283/277400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (11217/100000 : ℝ)) (hi := (13991/100000 : ℝ)) (c := (13865006182317991523/13870000000000000000 : ℝ)) (alpha := (538184085283/277400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1107571779/5000000000 : ℝ)*X 0 0+(269737887/500000000 : ℝ)*X 0 1+(5264020923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167032113/312500000 : ℝ)*X 1 0+(-1140740813/5000000000 : ℝ)*X 1 1+(2632010461/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345027613/10000000000 : ℝ)*X 2 0+(5264020931/10000000000 : ℝ)*X 2 1+(-1140740809/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378810369/10000000000 : ℝ)*X 0 0+(850634757/2000000000 : ℝ)*X 0 1+(4508230361/10000000000 : ℝ)*X 0 2+(4378810369/10000000000 : ℝ)*X 1 0+(850634757/2000000000 : ℝ)*X 1 1+(4508230361/10000000000 : ℝ)*X 1 2+(4378810369/10000000000 : ℝ)*X 2 0+(850634757/2000000000 : ℝ)*X 2 1+(4508230361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2215148667/10000000000 : ℝ)*X 0 0+(2632174059/5000000000 : ℝ)*X 0 1+(5394429379/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656079223/5000000000 : ℝ)*X 1 0+(-2151073089/10000000000 : ℝ)*X 1 1+(5394429333/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062431643/2000000000 : ℝ)*X 2 0+(5394429283/10000000000 : ℝ)*X 2 1+(-537768367/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378819989/10000000000 : ℝ)*X 0 0+(901518413/2000000000 : ℝ)*X 0 1+(106345369/250000000 : ℝ)*X 0 2+(4378819989/10000000000 : ℝ)*X 1 0+(901518413/2000000000 : ℝ)*X 1 1+(106345369/250000000 : ℝ)*X 1 2+(4378819989/10000000000 : ℝ)*X 2 0+(901518413/2000000000 : ℝ)*X 2 1+(106345369/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6161691696157682622392895039/693500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1794149817/100000000000000 : ℝ)*(base19) + (82608559/5000000000000 : ℝ)*(base23) + (36796629/50000000000000 : ℝ)*(lower2) + (112025143/50000000000000 : ℝ)*(upper3) + (132926559/100000000000000 : ℝ)*(upper5) + (5784901017681369/100000000000000 : ℝ)*(major0) + (5784901017681369/100000000000000 : ℝ)*(major1) + (5784901017681369/100000000000000 : ℝ)*(major2) + (1912251200242309/25000000000000 : ℝ)*(sp0) + (7649050924755571/100000000000000 : ℝ)*(sp1) + (59758211458861/781250000000 : ℝ)*(sp2) + (490090318750663/12500000000000 : ℝ)*(sp3) + (47917936153/100000000000000 : ℝ)*(sp4) + (26470288053/100000000000000 : ℝ)*(sp7) + (3920749020293357/100000000000000 : ℝ)*(f.failure) + (1912263179726347/25000000000000 : ℝ)*(f.sum) + (57951332587447/13870000000000000000000000000 : ℝ)*base65 + (21729771098605384987/1387000000000000000000000000000000 : ℝ)*base67 + (4308808567614615013/1387000000000000000000000000000000 : ℝ)*base70 + (4447909840755384987/1387000000000000000000000000000000 : ℝ)*base71 + (18879698590503/13870000000000000000000000000 : ℝ)*base74 + (17772823469003615013/1387000000000000000000000000000000 : ℝ)*base76 + (1054147243539384987/1387000000000000000000000000000000 : ℝ)*base77 + (10879116205407384987/1387000000000000000000000000000000 : ℝ)*base79 + (72832498425173/13870000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (42935759/10000000000000000000000 : ℝ)*base90 + (42935759/10000000000000000000000 : ℝ)*base92 + (42935759/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2111376813147585993871675839/173375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2109537571/100000000000000 : ℝ)*(base19) + (209387261/12500000000000 : ℝ)*(base23) + (38876153/100000000000000 : ℝ)*(upper2) + (51326201/50000000000000 : ℝ)*(upper3) + (55271487/25000000000000 : ℝ)*(upper5) + (1453494920462723/25000000000000 : ℝ)*(major0) + (1453494920462723/25000000000000 : ℝ)*(major1) + (1453494920462723/25000000000000 : ℝ)*(major2) + (12783646689/20000000000000 : ℝ)*(sp1) + (1795254799/5000000000000 : ℝ)*(sp2) + (768750171019107/10000000000000 : ℝ)*(sp4) + (1537487136484011/20000000000000 : ℝ)*(sp5) + (3843732064998501/50000000000000 : ℝ)*(sp6) + (1970228623787139/50000000000000 : ℝ)*(sp7) + (1970228623787139/50000000000000 : ℝ)*(f.failure) + (768750171019107/10000000000000 : ℝ)*(f.sum) + (24332309299299/3467500000000000000000000000 : ℝ)*base65 + (580295654504447129/346750000000000000000000000000000 : ℝ)*base67 + (6013147441564447129/346750000000000000000000000000000 : ℝ)*base69 + (2962057511655947129/346750000000000000000000000000000 : ℝ)*base71 + (28431871545543/6935000000000000000000000000 : ℝ)*base73 + (3527586548558197129/346750000000000000000000000000000 : ℝ)*base75 + (4949935205095947129/346750000000000000000000000000000 : ℝ)*base77 + (9665124611633947129/346750000000000000000000000000000 : ℝ)*base79 + (17770185344489/3467500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (37300993/5000000000000000000000 : ℝ)*base90 + (37300993/5000000000000000000000 : ℝ)*base92 + (37300993/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1043_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13991/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1043_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1043_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1043_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1043_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1043_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1043_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

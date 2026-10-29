-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1472_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:10:56.755716+00:00
-- url     : https://prove2.me/submissions/bc581402-bb5d-4e95-9e05-4a09240898ee

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
theorem support_rectangle_w1472_s0_0 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-345818903/2000000000 : ℝ)*x 0 + (1486074473/2500000000 : ℝ)*x 1 + (4837837941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (345818903/2000000000 : ℝ)^4441 ≤ (408761237851/4000000000000 : ℝ)^3417 := by
    have hnat : (345818903 : ℕ)^4441*4000000000000^3417 ≤ 408761237851^3417*2000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345818903 2000000000 408761237851 4000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1486074473/2500000000 : ℝ)^4441 ≤ (6357896732493/12500000000000 : ℝ)^3417 := by
    have hnat : (1486074473 : ℕ)^4441*12500000000000^3417 ≤ 6357896732493^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1486074473 2500000000 6357896732493 12500000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4837837941/10000000000 : ℝ)^4441 ≤ (311342361383/800000000000 : ℝ)^3417 := by
    have hnat : (4837837941 : ℕ)^4441*800000000000^3417 ≤ 311342361383^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4837837941 10000000000 311342361383 800000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-345818903/2000000000 : ℝ), (1486074473/2500000000 : ℝ), (4837837941/10000000000 : ℝ)] ![(408761237851/4000000000000 : ℝ), (6357896732493/12500000000000 : ℝ), (311342361383/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-345818903/2000000000 : ℝ)|^4441 ≤ (408761237851/4000000000000 : ℝ)^3417
        have hw : |(-345818903/2000000000 : ℝ)|=(345818903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1486074473/2500000000 : ℝ)|^4441 ≤ (6357896732493/12500000000000 : ℝ)^3417
        have hw : |(1486074473/2500000000 : ℝ)|=(1486074473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4837837941/10000000000 : ℝ)|^4441 ≤ (311342361383/800000000000 : ℝ)^3417
        have hw : |(4837837941/10000000000 : ℝ)|=(4837837941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s0_1 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2743366793/5000000000 : ℝ)*x 0 + (-1176281903/5000000000 : ℝ)*x 1 + (4837837807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2743366793/5000000000 : ℝ)^4441 ≤ (45834442690293/100000000000000 : ℝ)^3417 := by
    have hnat : (2743366793 : ℕ)^4441*100000000000000^3417 ≤ 45834442690293^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743366793 5000000000 45834442690293 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1176281903/5000000000 : ℝ)^4441 ≤ (1905970439837/12500000000000 : ℝ)^3417 := by
    have hnat : (1176281903 : ℕ)^4441*12500000000000^3417 ≤ 1905970439837^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1176281903 5000000000 1905970439837 12500000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4837837807/10000000000 : ℝ)^4441 ≤ (38917793771877/100000000000000 : ℝ)^3417 := by
    have hnat : (4837837807 : ℕ)^4441*100000000000000^3417 ≤ 38917793771877^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4837837807 10000000000 38917793771877 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2743366793/5000000000 : ℝ), (-1176281903/5000000000 : ℝ), (4837837807/10000000000 : ℝ)] ![(45834442690293/100000000000000 : ℝ), (1905970439837/12500000000000 : ℝ), (38917793771877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2743366793/5000000000 : ℝ)|^4441 ≤ (45834442690293/100000000000000 : ℝ)^3417
        have hw : |(2743366793/5000000000 : ℝ)|=(2743366793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1176281903/5000000000 : ℝ)|^4441 ≤ (1905970439837/12500000000000 : ℝ)^3417
        have hw : |(-1176281903/5000000000 : ℝ)|=(1176281903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4837837807/10000000000 : ℝ)|^4441 ≤ (38917793771877/100000000000000 : ℝ)^3417
        have hw : |(4837837807/10000000000 : ℝ)|=(4837837807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s0_2 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2743366789/5000000000 : ℝ)*x 0 + (4837838179/10000000000 : ℝ)*x 1 + (-588140839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2743366789/5000000000 : ℝ)^4441 ≤ (11458610650859/25000000000000 : ℝ)^3417 := by
    have hnat : (2743366789 : ℕ)^4441*25000000000000^3417 ≤ 11458610650859^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743366789 5000000000 11458610650859 25000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4837838179/10000000000 : ℝ)^4441 ≤ (19458898830607/50000000000000 : ℝ)^3417 := by
    have hnat : (4837838179 : ℕ)^4441*50000000000000^3417 ≤ 19458898830607^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4837838179 10000000000 19458898830607 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (588140839/2500000000 : ℝ)^4441 ≤ (3811939932013/25000000000000 : ℝ)^3417 := by
    have hnat : (588140839 : ℕ)^4441*25000000000000^3417 ≤ 3811939932013^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588140839 2500000000 3811939932013 25000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2743366789/5000000000 : ℝ), (4837838179/10000000000 : ℝ), (-588140839/2500000000 : ℝ)] ![(11458610650859/25000000000000 : ℝ), (19458898830607/50000000000000 : ℝ), (3811939932013/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2743366789/5000000000 : ℝ)|^4441 ≤ (11458610650859/25000000000000 : ℝ)^3417
        have hw : |(2743366789/5000000000 : ℝ)|=(2743366789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4837838179/10000000000 : ℝ)|^4441 ≤ (19458898830607/50000000000000 : ℝ)^3417
        have hw : |(4837838179/10000000000 : ℝ)|=(4837838179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-588140839/2500000000 : ℝ)|^4441 ≤ (3811939932013/25000000000000 : ℝ)^3417
        have hw : |(-588140839/2500000000 : ℝ)|=(588140839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s0_3 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2078055211/5000000000 : ℝ)*x 0 + (772921437/2500000000 : ℝ)*x 1 + (2765062387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2078055211/5000000000 : ℝ)^4441 ≤ (3993245087963/12500000000000 : ℝ)^3417 := by
    have hnat : (2078055211 : ℕ)^4441*12500000000000^3417 ≤ 3993245087963^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078055211 5000000000 3993245087963 12500000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (772921437/2500000000 : ℝ)^4441 ≤ (21747936855611/100000000000000 : ℝ)^3417 := by
    have hnat : (772921437 : ℕ)^4441*100000000000000^3417 ≤ 21747936855611^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772921437 2500000000 21747936855611 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2765062387/5000000000 : ℝ)^4441 ≤ (1157652560529/2500000000000 : ℝ)^3417 := by
    have hnat : (2765062387 : ℕ)^4441*2500000000000^3417 ≤ 1157652560529^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2765062387 5000000000 1157652560529 2500000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2078055211/5000000000 : ℝ), (772921437/2500000000 : ℝ), (2765062387/5000000000 : ℝ)] ![(3993245087963/12500000000000 : ℝ), (21747936855611/100000000000000 : ℝ), (1157652560529/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2078055211/5000000000 : ℝ)|^4441 ≤ (3993245087963/12500000000000 : ℝ)^3417
        have hw : |(2078055211/5000000000 : ℝ)|=(2078055211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(772921437/2500000000 : ℝ)|^4441 ≤ (21747936855611/100000000000000 : ℝ)^3417
        have hw : |(772921437/2500000000 : ℝ)|=(772921437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2765062387/5000000000 : ℝ)|^4441 ≤ (1157652560529/2500000000000 : ℝ)^3417
        have hw : |(2765062387/5000000000 : ℝ)|=(2765062387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s0_4 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1732971191/10000000000 : ℝ)*x 0 + (4866261443/10000000000 : ℝ)*x 1 + (1182970369/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1732971191/10000000000 : ℝ)^4441 ≤ (10248818310697/100000000000000 : ℝ)^3417 := by
    have hnat : (1732971191 : ℕ)^4441*100000000000000^3417 ≤ 10248818310697^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732971191 10000000000 10248818310697 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4866261443/10000000000 : ℝ)^4441 ≤ (19607615037303/50000000000000 : ℝ)^3417 := by
    have hnat : (4866261443 : ℕ)^4441*50000000000000^3417 ≤ 19607615037303^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4866261443 10000000000 19607615037303 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1182970369/2000000000 : ℝ)^4441 ≤ (3158496975131/6250000000000 : ℝ)^3417 := by
    have hnat : (1182970369 : ℕ)^4441*6250000000000^3417 ≤ 3158496975131^3417*2000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182970369 2000000000 3158496975131 6250000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1732971191/10000000000 : ℝ), (4866261443/10000000000 : ℝ), (1182970369/2000000000 : ℝ)] ![(10248818310697/100000000000000 : ℝ), (19607615037303/50000000000000 : ℝ), (3158496975131/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1732971191/10000000000 : ℝ)|^4441 ≤ (10248818310697/100000000000000 : ℝ)^3417
        have hw : |(-1732971191/10000000000 : ℝ)|=(1732971191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4866261443/10000000000 : ℝ)|^4441 ≤ (19607615037303/50000000000000 : ℝ)^3417
        have hw : |(4866261443/10000000000 : ℝ)|=(4866261443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1182970369/2000000000 : ℝ)|^4441 ≤ (3158496975131/6250000000000 : ℝ)^3417
        have hw : |(1182970369/2000000000 : ℝ)|=(1182970369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s0_5 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5184675057/10000000000 : ℝ)*x 0 + (-637774523/5000000000 : ℝ)*x 1 + (46209781/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184675057/10000000000 : ℝ)^4441 ≤ (42582371283191/100000000000000 : ℝ)^3417 := by
    have hnat : (5184675057 : ℕ)^4441*100000000000000^3417 ≤ 42582371283191^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184675057 10000000000 42582371283191 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (637774523/5000000000 : ℝ)^4441 ≤ (1720418933669/25000000000000 : ℝ)^3417 := by
    have hnat : (637774523 : ℕ)^4441*25000000000000^3417 ≤ 1720418933669^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637774523 5000000000 1720418933669 25000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46209781/78125000 : ℝ)^4441 ≤ (6316994120991/12500000000000 : ℝ)^3417 := by
    have hnat : (46209781 : ℕ)^4441*12500000000000^3417 ≤ 6316994120991^3417*78125000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46209781 78125000 6316994120991 12500000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184675057/10000000000 : ℝ), (-637774523/5000000000 : ℝ), (46209781/78125000 : ℝ)] ![(42582371283191/100000000000000 : ℝ), (1720418933669/25000000000000 : ℝ), (6316994120991/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184675057/10000000000 : ℝ)|^4441 ≤ (42582371283191/100000000000000 : ℝ)^3417
        have hw : |(5184675057/10000000000 : ℝ)|=(5184675057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-637774523/5000000000 : ℝ)|^4441 ≤ (1720418933669/25000000000000 : ℝ)^3417
        have hw : |(-637774523/5000000000 : ℝ)|=(637774523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(46209781/78125000 : ℝ)|^4441 ≤ (6316994120991/12500000000000 : ℝ)^3417
        have hw : |(46209781/78125000 : ℝ)|=(46209781/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s0_6 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1036934999/2000000000 : ℝ)*x 0 + (5914851831/10000000000 : ℝ)*x 1 + (-637774679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036934999/2000000000 : ℝ)^4441 ≤ (21291185310689/50000000000000 : ℝ)^3417 := by
    have hnat : (1036934999 : ℕ)^4441*50000000000000^3417 ≤ 21291185310689^3417*2000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036934999 2000000000 21291185310689 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5914851831/10000000000 : ℝ)^4441 ≤ (10107190289327/20000000000000 : ℝ)^3417 := by
    have hnat : (5914851831 : ℕ)^4441*20000000000000^3417 ≤ 10107190289327^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5914851831 10000000000 10107190289327 20000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637774679/5000000000 : ℝ)^4441 ≤ (55053423379/800000000000 : ℝ)^3417 := by
    have hnat : (637774679 : ℕ)^4441*800000000000^3417 ≤ 55053423379^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637774679 5000000000 55053423379 800000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036934999/2000000000 : ℝ), (5914851831/10000000000 : ℝ), (-637774679/5000000000 : ℝ)] ![(21291185310689/50000000000000 : ℝ), (10107190289327/20000000000000 : ℝ), (55053423379/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036934999/2000000000 : ℝ)|^4441 ≤ (21291185310689/50000000000000 : ℝ)^3417
        have hw : |(1036934999/2000000000 : ℝ)|=(1036934999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5914851831/10000000000 : ℝ)|^4441 ≤ (10107190289327/20000000000000 : ℝ)^3417
        have hw : |(5914851831/10000000000 : ℝ)|=(5914851831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-637774679/5000000000 : ℝ)|^4441 ≤ (55053423379/800000000000 : ℝ)^3417
        have hw : |(-637774679/5000000000 : ℝ)|=(637774679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s0_7 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4164655847/10000000000 : ℝ)*x 0 + (5467484653/10000000000 : ℝ)*x 1 + (3156579859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4164655847/10000000000 : ℝ)^4441 ≤ (32031355626831/100000000000000 : ℝ)^3417 := by
    have hnat : (4164655847 : ℕ)^4441*100000000000000^3417 ≤ 32031355626831^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164655847 10000000000 32031355626831 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467484653/10000000000 : ℝ)^4441 ≤ (22812782515563/50000000000000 : ℝ)^3417 := by
    have hnat : (5467484653 : ℕ)^4441*50000000000000^3417 ≤ 22812782515563^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467484653 10000000000 22812782515563 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3156579859/10000000000 : ℝ)^4441 ≤ (22343079329197/100000000000000 : ℝ)^3417 := by
    have hnat : (3156579859 : ℕ)^4441*100000000000000^3417 ≤ 22343079329197^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3156579859 10000000000 22343079329197 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4164655847/10000000000 : ℝ), (5467484653/10000000000 : ℝ), (3156579859/10000000000 : ℝ)] ![(32031355626831/100000000000000 : ℝ), (22812782515563/50000000000000 : ℝ), (22343079329197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4164655847/10000000000 : ℝ)|^4441 ≤ (32031355626831/100000000000000 : ℝ)^3417
        have hw : |(4164655847/10000000000 : ℝ)|=(4164655847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467484653/10000000000 : ℝ)|^4441 ≤ (22812782515563/50000000000000 : ℝ)^3417
        have hw : |(5467484653/10000000000 : ℝ)|=(5467484653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3156579859/10000000000 : ℝ)|^4441 ≤ (22343079329197/100000000000000 : ℝ)^3417
        have hw : |(3156579859/10000000000 : ℝ)|=(3156579859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1472_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2297/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6503/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4439/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4439 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4439*1^1024 ≤ 0^1024*1^4439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4439/1024 : ℝ) ≤ (235426648410778743/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4439 ≤ (235426648410778743/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4439*12500000000000000000^1024 ≤ 235426648410778743^1024*5^4439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 235426648410778743 12500000000000000000 4439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (235426648410778743/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4439 := by
      have hnat : (1 : ℕ)^1024*1^4439 ≤ 1^4439*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12735426648410778743/12500000000000000000 : ℝ) ≤ (1255391969046037/1250000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (12735426648410778743/12500000000000000000 : ℝ)^1024 ≤ (1255391969046037/1250000000000000 : ℝ)^4439 := by
      have hnat : (12735426648410778743 : ℕ)^1024*1250000000000000^4439 ≤ 1255391969046037^4439*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12735426648410778743 12500000000000000000 1255391969046037 1250000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1255391969046037/1250000000000000 : ℝ)) (X := (12735426648410778743/12500000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6485426648410778743/6250000000000000000 : ℝ) ≤ (630391969046037/625000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (6485426648410778743/6250000000000000000 : ℝ)^1024 ≤ (630391969046037/625000000000000 : ℝ)^4439 := by
      have hnat : (6485426648410778743 : ℕ)^1024*625000000000000^4439 ≤ 630391969046037^4439*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6485426648410778743 6250000000000000000 630391969046037 625000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (630391969046037/625000000000000 : ℝ)) (X := (6485426648410778743/6250000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5391969046037/500000000000000 : ℝ)*(0 : ℝ))^(4439/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5391969046037/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(235426648410778743/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5391969046037/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4439/1024 : ℝ) := by
    rw [show (1 : ℝ)+(5391969046037/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1255391969046037/1250000000000000 : ℝ) by norm_num, show 1+(235426648410778743/12500000000000000000 : ℝ)+(0 : ℝ)=(12735426648410778743/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(235426648410778743/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5391969046037/500000000000000 : ℝ)*(2/5 : ℝ))^(4439/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5391969046037/500000000000000 : ℝ)*(2/5 : ℝ)=(630391969046037/625000000000000 : ℝ) by norm_num, show 1+2*(235426648410778743/12500000000000000000 : ℝ)=(6485426648410778743/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5391969046037/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5391969046037/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5391969046037/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5391969046037/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5391969046037/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5391969046037/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-345818903/2000000000 : ℝ)*X 0 0+(1486074473/2500000000 : ℝ)*X 0 1+(4837837941/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2743366793/5000000000 : ℝ)*X 1 0+(-1176281903/5000000000 : ℝ)*X 1 1+(4837837807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2743366789/5000000000 : ℝ)*X 2 0+(4837838179/10000000000 : ℝ)*X 2 1+(-588140839/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2078055211/5000000000 : ℝ)*X 0 0+(772921437/2500000000 : ℝ)*X 0 1+(2765062387/5000000000 : ℝ)*X 0 2+(2078055211/5000000000 : ℝ)*X 1 0+(772921437/2500000000 : ℝ)*X 1 1+(2765062387/5000000000 : ℝ)*X 1 2+(2078055211/5000000000 : ℝ)*X 2 0+(772921437/2500000000 : ℝ)*X 2 1+(2765062387/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1732971191/10000000000 : ℝ)*X 0 0+(4866261443/10000000000 : ℝ)*X 0 1+(1182970369/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5184675057/10000000000 : ℝ)*X 1 0+(-637774523/5000000000 : ℝ)*X 1 1+(46209781/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1036934999/2000000000 : ℝ)*X 2 0+(5914851831/10000000000 : ℝ)*X 2 1+(-637774679/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4164655847/10000000000 : ℝ)*X 0 0+(5467484653/10000000000 : ℝ)*X 0 1+(3156579859/10000000000 : ℝ)*X 0 2+(4164655847/10000000000 : ℝ)*X 1 0+(5467484653/10000000000 : ℝ)*X 1 1+(3156579859/10000000000 : ℝ)*X 1 2+(4164655847/10000000000 : ℝ)*X 2 0+(5467484653/10000000000 : ℝ)*X 2 1+(3156579859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3431770561968965697/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (206517223/12500000000000 : ℝ)*(base19) + (1613253553/100000000000000 : ℝ)*(base23) + (23320367/12500000000000 : ℝ)*(upper3) + (20611707/100000000000000 : ℝ)*(upper4) + (275422967/100000000000000 : ℝ)*(upper5) + (26277964659087/4000000000000 : ℝ)*(major0) + (26277964659087/4000000000000 : ℝ)*(major1) + (26277964659087/4000000000000 : ℝ)*(major2) + (90378835239267/10000000000000 : ℝ)*(sp0) + (225948193582973/25000000000000 : ℝ)*(sp1) + (903792813216123/100000000000000 : ℝ)*(sp2) + (25631315752933/6250000000000 : ℝ)*(sp3) + (1214815401/20000000000000 : ℝ)*(sp4) + (1262826519/50000000000000 : ℝ)*(sp7) + (205051788849983/50000000000000 : ℝ)*(f.failure) + (225948606617419/25000000000000 : ℝ)*(f.sum) + (1641184591219/1000000000000000000000000000 : ℝ)*base65 + (1217242237781/2000000000000000000000000000 : ℝ)*base68 + (8793368170219/2000000000000000000000000000 : ℝ)*base69 + (2048870360219/2000000000000000000000000000 : ℝ)*base71 + (1310593617781/1000000000000000000000000000 : ℝ)*base74 + (10268280127781/2000000000000000000000000000 : ℝ)*base76 + (5326636403781/2000000000000000000000000000 : ℝ)*base78 + (7109422561781/2000000000000000000000000000 : ℝ)*base80 + (4293146262219/1000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (20302609/5000000000000000000000 : ℝ)*base89 + (20302609/5000000000000000000000 : ℝ)*base91 + (20302609/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10505247171060931889829/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (394040707/50000000000000 : ℝ)*(base19) + (154316337/20000000000000 : ℝ)*(base23) + (11864067/12500000000000 : ℝ)*(base32) + (119211679/100000000000000 : ℝ)*(upper3) + (64504449/100000000000000 : ℝ)*(upper5) + (21662369837917/3125000000000 : ℝ)*(major0) + (21662369837917/3125000000000 : ℝ)*(major1) + (21662369837917/3125000000000 : ℝ)*(major2) + (1991257691/100000000000000 : ℝ)*(sp1) + (4759487/250000000000 : ℝ)*(sp2) + (953660795364801/100000000000000 : ℝ)*(sp4) + (29801813000803/3125000000000 : ℝ)*(sp5) + (238414529997079/25000000000000 : ℝ)*(sp6) + (432730667293373/100000000000000 : ℝ)*(sp7) + (432730762205909/100000000000000 : ℝ)*(f.failure) + (953660795364801/100000000000000 : ℝ)*(f.sum) + (202237458663/97656250000000000000000000 : ℝ)*base65 + (3771656791179/1562500000000000000000000000 : ℝ)*base67 + (1041797666179/1562500000000000000000000000 : ℝ)*base69 + (16012675716733/3125000000000000000000000000 : ℝ)*base71 + (4015065907159/3125000000000000000000000000 : ℝ)*base74 + (10603382791179/1562500000000000000000000000 : ℝ)*base75 + (8117743772983/3125000000000000000000000000 : ℝ)*base77 + (30083288729233/3125000000000000000000000000 : ℝ)*base79 + (2687684257159/3125000000000000000000000000 : ℝ)*base82 + (100645093/10000000000000000000000 : ℝ)*base90 + (100645093/10000000000000000000000 : ℝ)*base92 + (100645093/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1472_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2297/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6503/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1472_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1472_s1_0 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-189370961/1000000000 : ℝ)*x 0 + (559859929/1000000000 : ℝ)*x 1 + (1269476541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (189370961/1000000000 : ℝ)^4441 ≤ (287527940653/2500000000000 : ℝ)^3417 := by
    have hnat : (189370961 : ℕ)^4441*2500000000000^3417 ≤ 287527940653^3417*1000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189370961 1000000000 287527940653 2500000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559859929/1000000000 : ℝ)^4441 ≤ (23526336404417/50000000000000 : ℝ)^3417 := by
    have hnat : (559859929 : ℕ)^4441*50000000000000^3417 ≤ 23526336404417^3417*1000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559859929 1000000000 23526336404417 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1269476541/2500000000 : ℝ)^4441 ≤ (41446209551393/100000000000000 : ℝ)^3417 := by
    have hnat : (1269476541 : ℕ)^4441*100000000000000^3417 ≤ 41446209551393^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269476541 2500000000 41446209551393 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-189370961/1000000000 : ℝ), (559859929/1000000000 : ℝ), (1269476541/2500000000 : ℝ)] ![(287527940653/2500000000000 : ℝ), (23526336404417/50000000000000 : ℝ), (41446209551393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-189370961/1000000000 : ℝ)|^4441 ≤ (287527940653/2500000000000 : ℝ)^3417
        have hw : |(-189370961/1000000000 : ℝ)|=(189370961/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559859929/1000000000 : ℝ)|^4441 ≤ (23526336404417/50000000000000 : ℝ)^3417
        have hw : |(559859929/1000000000 : ℝ)|=(559859929/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1269476541/2500000000 : ℝ)|^4441 ≤ (41446209551393/100000000000000 : ℝ)^3417
        have hw : |(1269476541/2500000000 : ℝ)|=(1269476541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s1_1 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394082867/10000000000 : ℝ)*x 0 + (-2169339833/10000000000 : ℝ)*x 1 + (2538953661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394082867/10000000000 : ℝ)^4441 ≤ (5603884973717/12500000000000 : ℝ)^3417 := by
    have hnat : (5394082867 : ℕ)^4441*12500000000000^3417 ≤ 5603884973717^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394082867 10000000000 5603884973717 12500000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2169339833/10000000000 : ℝ)^4441 ≤ (13722698363431/100000000000000 : ℝ)^3417 := by
    have hnat : (2169339833 : ℕ)^4441*100000000000000^3417 ≤ 13722698363431^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169339833 10000000000 13722698363431 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2538953661/5000000000 : ℝ)^4441 ≤ (20723110917763/50000000000000 : ℝ)^3417 := by
    have hnat : (2538953661 : ℕ)^4441*50000000000000^3417 ≤ 20723110917763^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538953661 5000000000 20723110917763 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394082867/10000000000 : ℝ), (-2169339833/10000000000 : ℝ), (2538953661/5000000000 : ℝ)] ![(5603884973717/12500000000000 : ℝ), (13722698363431/100000000000000 : ℝ), (20723110917763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394082867/10000000000 : ℝ)|^4441 ≤ (5603884973717/12500000000000 : ℝ)^3417
        have hw : |(5394082867/10000000000 : ℝ)|=(5394082867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2169339833/10000000000 : ℝ)|^4441 ≤ (13722698363431/100000000000000 : ℝ)^3417
        have hw : |(-2169339833/10000000000 : ℝ)|=(2169339833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2538953661/5000000000 : ℝ)|^4441 ≤ (20723110917763/50000000000000 : ℝ)^3417
        have hw : |(2538953661/5000000000 : ℝ)|=(2538953661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s1_2 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394083777/10000000000 : ℝ)*x 0 + (5077906631/10000000000 : ℝ)*x 1 + (-271167441/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394083777/10000000000 : ℝ)^4441 ≤ (22415544809701/50000000000000 : ℝ)^3417 := by
    have hnat : (5394083777 : ℕ)^4441*50000000000000^3417 ≤ 22415544809701^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394083777 10000000000 22415544809701 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5077906631/10000000000 : ℝ)^4441 ≤ (41446214505357/100000000000000 : ℝ)^3417 := by
    have hnat : (5077906631 : ℕ)^4441*100000000000000^3417 ≤ 41446214505357^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077906631 10000000000 41446214505357 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271167441/1250000000 : ℝ)^4441 ≤ (3430673963973/25000000000000 : ℝ)^3417 := by
    have hnat : (271167441 : ℕ)^4441*25000000000000^3417 ≤ 3430673963973^3417*1250000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271167441 1250000000 3430673963973 25000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394083777/10000000000 : ℝ), (5077906631/10000000000 : ℝ), (-271167441/1250000000 : ℝ)] ![(22415544809701/50000000000000 : ℝ), (41446214505357/100000000000000 : ℝ), (3430673963973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394083777/10000000000 : ℝ)|^4441 ≤ (22415544809701/50000000000000 : ℝ)^3417
        have hw : |(5394083777/10000000000 : ℝ)|=(5394083777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5077906631/10000000000 : ℝ)|^4441 ≤ (41446214505357/100000000000000 : ℝ)^3417
        have hw : |(5077906631/10000000000 : ℝ)|=(5077906631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271167441/1250000000 : ℝ)|^4441 ≤ (3430673963973/25000000000000 : ℝ)^3417
        have hw : |(-271167441/1250000000 : ℝ)|=(271167441/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s1_3 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213208461/500000000 : ℝ)*x 0 + (3724098169/10000000000 : ℝ)*x 1 + (2435805117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213208461/500000000 : ℝ)^4441 ≤ (33029646364713/100000000000000 : ℝ)^3417 := by
    have hnat : (213208461 : ℕ)^4441*100000000000000^3417 ≤ 33029646364713^3417*500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213208461 500000000 33029646364713 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3724098169/10000000000 : ℝ)^4441 ≤ (27699093334183/100000000000000 : ℝ)^3417 := by
    have hnat : (3724098169 : ℕ)^4441*100000000000000^3417 ≤ 27699093334183^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3724098169 10000000000 27699093334183 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2435805117/5000000000 : ℝ)^4441 ≤ (39271260285217/100000000000000 : ℝ)^3417 := by
    have hnat : (2435805117 : ℕ)^4441*100000000000000^3417 ≤ 39271260285217^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2435805117 5000000000 39271260285217 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213208461/500000000 : ℝ), (3724098169/10000000000 : ℝ), (2435805117/5000000000 : ℝ)] ![(33029646364713/100000000000000 : ℝ), (27699093334183/100000000000000 : ℝ), (39271260285217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213208461/500000000 : ℝ)|^4441 ≤ (33029646364713/100000000000000 : ℝ)^3417
        have hw : |(213208461/500000000 : ℝ)|=(213208461/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3724098169/10000000000 : ℝ)|^4441 ≤ (27699093334183/100000000000000 : ℝ)^3417
        have hw : |(3724098169/10000000000 : ℝ)|=(3724098169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2435805117/5000000000 : ℝ)|^4441 ≤ (39271260285217/100000000000000 : ℝ)^3417
        have hw : |(2435805117/5000000000 : ℝ)|=(2435805117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s1_4 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-947049017/5000000000 : ℝ)*x 0 + (1016813759/2000000000 : ℝ)*x 1 + (5592331489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (947049017/5000000000 : ℝ)^4441 ≤ (11504183694663/100000000000000 : ℝ)^3417 := by
    have hnat : (947049017 : ℕ)^4441*100000000000000^3417 ≤ 11504183694663^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947049017 5000000000 11504183694663 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016813759/2000000000 : ℝ)^4441 ≤ (41511594991541/100000000000000 : ℝ)^3417 := by
    have hnat : (1016813759 : ℕ)^4441*100000000000000^3417 ≤ 41511594991541^3417*2000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016813759 2000000000 41511594991541 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5592331489/10000000000 : ℝ)^4441 ≤ (23492110649673/50000000000000 : ℝ)^3417 := by
    have hnat : (5592331489 : ℕ)^4441*50000000000000^3417 ≤ 23492110649673^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5592331489 10000000000 23492110649673 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-947049017/5000000000 : ℝ), (1016813759/2000000000 : ℝ), (5592331489/10000000000 : ℝ)] ![(11504183694663/100000000000000 : ℝ), (41511594991541/100000000000000 : ℝ), (23492110649673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-947049017/5000000000 : ℝ)|^4441 ≤ (11504183694663/100000000000000 : ℝ)^3417
        have hw : |(-947049017/5000000000 : ℝ)|=(947049017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016813759/2000000000 : ℝ)|^4441 ≤ (41511594991541/100000000000000 : ℝ)^3417
        have hw : |(1016813759/2000000000 : ℝ)|=(1016813759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5592331489/10000000000 : ℝ)|^4441 ≤ (23492110649673/50000000000000 : ℝ)^3417
        have hw : |(5592331489/10000000000 : ℝ)|=(5592331489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s1_5 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051527323/2000000000 : ℝ)*x 0 + (-1654915263/10000000000 : ℝ)*x 1 + (5592331511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051527323/2000000000 : ℝ)^4441 ≤ (5420353765651/12500000000000 : ℝ)^3417 := by
    have hnat : (1051527323 : ℕ)^4441*12500000000000^3417 ≤ 5420353765651^3417*2000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051527323 2000000000 5420353765651 12500000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1654915263/10000000000 : ℝ)^4441 ≤ (9652948327011/100000000000000 : ℝ)^3417 := by
    have hnat : (1654915263 : ℕ)^4441*100000000000000^3417 ≤ 9652948327011^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1654915263 10000000000 9652948327011 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5592331511/10000000000 : ℝ)^4441 ≤ (4698422153957/10000000000000 : ℝ)^3417 := by
    have hnat : (5592331511 : ℕ)^4441*10000000000000^3417 ≤ 4698422153957^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5592331511 10000000000 4698422153957 10000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051527323/2000000000 : ℝ), (-1654915263/10000000000 : ℝ), (5592331511/10000000000 : ℝ)] ![(5420353765651/12500000000000 : ℝ), (9652948327011/100000000000000 : ℝ), (4698422153957/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051527323/2000000000 : ℝ)|^4441 ≤ (5420353765651/12500000000000 : ℝ)^3417
        have hw : |(1051527323/2000000000 : ℝ)|=(1051527323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1654915263/10000000000 : ℝ)|^4441 ≤ (9652948327011/100000000000000 : ℝ)^3417
        have hw : |(-1654915263/10000000000 : ℝ)|=(1654915263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5592331511/10000000000 : ℝ)|^4441 ≤ (4698422153957/10000000000000 : ℝ)^3417
        have hw : |(5592331511/10000000000 : ℝ)|=(5592331511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s1_6 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257636669/10000000000 : ℝ)*x 0 + (349520717/625000000 : ℝ)*x 1 + (-827457621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257636669/10000000000 : ℝ)^4441 ≤ (8672566140809/20000000000000 : ℝ)^3417 := by
    have hnat : (5257636669 : ℕ)^4441*20000000000000^3417 ≤ 8672566140809^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257636669 10000000000 8672566140809 20000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349520717/625000000 : ℝ)^4441 ≤ (46984221113717/100000000000000 : ℝ)^3417 := by
    have hnat : (349520717 : ℕ)^4441*100000000000000^3417 ≤ 46984221113717^3417*625000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349520717 625000000 46984221113717 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827457621/5000000000 : ℝ)^4441 ≤ (9652948167813/100000000000000 : ℝ)^3417 := by
    have hnat : (827457621 : ℕ)^4441*100000000000000^3417 ≤ 9652948167813^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827457621 5000000000 9652948167813 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257636669/10000000000 : ℝ), (349520717/625000000 : ℝ), (-827457621/5000000000 : ℝ)] ![(8672566140809/20000000000000 : ℝ), (46984221113717/100000000000000 : ℝ), (9652948167813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257636669/10000000000 : ℝ)|^4441 ≤ (8672566140809/20000000000000 : ℝ)^3417
        have hw : |(5257636669/10000000000 : ℝ)|=(5257636669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(349520717/625000000 : ℝ)|^4441 ≤ (46984221113717/100000000000000 : ℝ)^3417
        have hw : |(349520717/625000000 : ℝ)|=(349520717/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-827457621/5000000000 : ℝ)|^4441 ≤ (9652948167813/100000000000000 : ℝ)^3417
        have hw : |(-827457621/5000000000 : ℝ)|=(827457621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s1_7 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533128267/1250000000 : ℝ)*x 0 + (4858030243/10000000000 : ℝ)*x 1 + (934477551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533128267/1250000000 : ℝ)^4441 ≤ (16519136650747/50000000000000 : ℝ)^3417 := by
    have hnat : (533128267 : ℕ)^4441*50000000000000^3417 ≤ 16519136650747^3417*1250000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533128267 1250000000 16519136650747 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4858030243/10000000000 : ℝ)^4441 ≤ (9782260451897/25000000000000 : ℝ)^3417 := by
    have hnat : (4858030243 : ℕ)^4441*25000000000000^3417 ≤ 9782260451897^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4858030243 10000000000 9782260451897 25000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (934477551/2500000000 : ℝ)^4441 ≤ (6958171219693/25000000000000 : ℝ)^3417 := by
    have hnat : (934477551 : ℕ)^4441*25000000000000^3417 ≤ 6958171219693^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934477551 2500000000 6958171219693 25000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533128267/1250000000 : ℝ), (4858030243/10000000000 : ℝ), (934477551/2500000000 : ℝ)] ![(16519136650747/50000000000000 : ℝ), (9782260451897/25000000000000 : ℝ), (6958171219693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533128267/1250000000 : ℝ)|^4441 ≤ (16519136650747/50000000000000 : ℝ)^3417
        have hw : |(533128267/1250000000 : ℝ)|=(533128267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4858030243/10000000000 : ℝ)|^4441 ≤ (9782260451897/25000000000000 : ℝ)^3417
        have hw : |(4858030243/10000000000 : ℝ)|=(4858030243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(934477551/2500000000 : ℝ)|^4441 ≤ (6958171219693/25000000000000 : ℝ)^3417
        have hw : |(934477551/2500000000 : ℝ)|=(934477551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1472_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2297/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3893/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18793/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6503/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2297/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6503/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2297/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6503/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2297/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6503/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2297/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6503/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2297/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6503/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2297/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2297/100000 : ℝ) ^ (4439/1024 : ℝ) ≤ (314598699253/4000000000000000000 : ℝ) := by
    have hpowers : (2297/100000 : ℝ)^4439 ≤ (314598699253/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2297 : ℕ)^4439*4000000000000000000^1024 ≤ 314598699253^1024*100000^4439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2297 100000 314598699253 4000000000000000000 4439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2297/100000 : ℝ)) (X := (314598699253/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6503/25000 : ℝ) ^ (4439/1024 : ℝ) ≤ (291609071991193509/100000000000000000000 : ℝ) := by
    have hpowers : (6503/25000 : ℝ)^4439 ≤ (291609071991193509/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6503 : ℕ)^4439*100000000000000000000^1024 ≤ 291609071991193509^1024*25000^4439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6503 25000 291609071991193509 100000000000000000000 4439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6503/25000 : ℝ)) (X := (291609071991193509/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000000314598699253/2000000000000000000 : ℝ) ≤ (5000000181431093/5000000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (2000000314598699253/2000000000000000000 : ℝ)^1024 ≤ (5000000181431093/5000000000000000 : ℝ)^4439 := by
      have hnat : (2000000314598699253 : ℕ)^1024*5000000000000000^4439 ≤ 5000000181431093^4439*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000000314598699253 2000000000000000000 5000000181431093 5000000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000181431093/5000000000000000 : ℝ)) (X := (2000000314598699253/2000000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50145808468479337417/50000000000000000000 : ℝ) ≤ (10006719561887047/10000000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (50145808468479337417/50000000000000000000 : ℝ)^1024 ≤ (10006719561887047/10000000000000000 : ℝ)^4439 := by
      have hnat : (50145808468479337417 : ℕ)^1024*10000000000000000^4439 ≤ 10006719561887047^4439*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50145808468479337417 50000000000000000000 10006719561887047 10000000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006719561887047/10000000000000000 : ℝ)) (X := (50145808468479337417/50000000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50291609071991193509/50000000000000000000 : ℝ) ≤ (2503359690227977/2500000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (50291609071991193509/50000000000000000000 : ℝ)^1024 ≤ (2503359690227977/2500000000000000 : ℝ)^4439 := by
      have hnat : (50291609071991193509 : ℕ)^1024*2500000000000000^4439 ≤ 2503359690227977^4439*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50291609071991193509 50000000000000000000 2503359690227977 2500000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503359690227977/2500000000000000 : ℝ)) (X := (50291609071991193509/50000000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(314598699253/4000000000000000000 : ℝ) ≤ ((6586642794582125821/6587500000000000000 : ℝ)+2*(746577669429/263500000000000 : ℝ)*(2297/100000 : ℝ))^(4439/1024 : ℝ) := by
    rw [show (6586642794582125821/6587500000000000000 : ℝ)+2*(746577669429/263500000000000 : ℝ)*(2297/100000 : ℝ)=(5000000181431093/5000000000000000 : ℝ) by norm_num, show 1+2*(314598699253/4000000000000000000 : ℝ)=(2000000314598699253/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(291609071991193509/100000000000000000000 : ℝ)+(314598699253/4000000000000000000 : ℝ) ≤ ((6586642794582125821/6587500000000000000 : ℝ)+(746577669429/263500000000000 : ℝ)*((6503/25000 : ℝ)+(2297/100000 : ℝ)))^(4439/1024 : ℝ) := by
    rw [show (6586642794582125821/6587500000000000000 : ℝ)+(746577669429/263500000000000 : ℝ)*((6503/25000 : ℝ)+(2297/100000 : ℝ))=(10006719561887047/10000000000000000 : ℝ) by norm_num, show 1+(291609071991193509/100000000000000000000 : ℝ)+(314598699253/4000000000000000000 : ℝ)=(50145808468479337417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(291609071991193509/100000000000000000000 : ℝ) ≤ ((6586642794582125821/6587500000000000000 : ℝ)+2*(746577669429/263500000000000 : ℝ)*(6503/25000 : ℝ))^(4439/1024 : ℝ) := by
    rw [show (6586642794582125821/6587500000000000000 : ℝ)+2*(746577669429/263500000000000 : ℝ)*(6503/25000 : ℝ)=(2503359690227977/2500000000000000 : ℝ) by norm_num, show 1+2*(291609071991193509/100000000000000000000 : ℝ)=(50291609071991193509/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6586642794582125821/6587500000000000000 : ℝ)*(X 1 0+X 2 0)+(746577669429/263500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (2297/100000 : ℝ)) (hi := (6503/25000 : ℝ)) (c := (6586642794582125821/6587500000000000000 : ℝ)) (alpha := (746577669429/263500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6586642794582125821/6587500000000000000 : ℝ)*(X 0 1+X 2 1)+(746577669429/263500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (2297/100000 : ℝ)) (hi := (6503/25000 : ℝ)) (c := (6586642794582125821/6587500000000000000 : ℝ)) (alpha := (746577669429/263500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6586642794582125821/6587500000000000000 : ℝ)*(X 0 2+X 1 2)+(746577669429/263500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (2297/100000 : ℝ)) (hi := (6503/25000 : ℝ)) (c := (6586642794582125821/6587500000000000000 : ℝ)) (alpha := (746577669429/263500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-189370961/1000000000 : ℝ)*X 0 0+(559859929/1000000000 : ℝ)*X 0 1+(1269476541/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5394082867/10000000000 : ℝ)*X 1 0+(-2169339833/10000000000 : ℝ)*X 1 1+(2538953661/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5394083777/10000000000 : ℝ)*X 2 0+(5077906631/10000000000 : ℝ)*X 2 1+(-271167441/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((213208461/500000000 : ℝ)*X 0 0+(3724098169/10000000000 : ℝ)*X 0 1+(2435805117/5000000000 : ℝ)*X 0 2+(213208461/500000000 : ℝ)*X 1 0+(3724098169/10000000000 : ℝ)*X 1 1+(2435805117/5000000000 : ℝ)*X 1 2+(213208461/500000000 : ℝ)*X 2 0+(3724098169/10000000000 : ℝ)*X 2 1+(2435805117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-947049017/5000000000 : ℝ)*X 0 0+(1016813759/2000000000 : ℝ)*X 0 1+(5592331489/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1051527323/2000000000 : ℝ)*X 1 0+(-1654915263/10000000000 : ℝ)*X 1 1+(5592331511/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257636669/10000000000 : ℝ)*X 2 0+(349520717/625000000 : ℝ)*X 2 1+(-827457621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((533128267/1250000000 : ℝ)*X 0 0+(4858030243/10000000000 : ℝ)*X 0 1+(934477551/2500000000 : ℝ)*X 0 2+(533128267/1250000000 : ℝ)*X 1 0+(4858030243/10000000000 : ℝ)*X 1 1+(934477551/2500000000 : ℝ)*X 1 2+(533128267/1250000000 : ℝ)*X 2 0+(4858030243/10000000000 : ℝ)*X 2 1+(934477551/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2411719541882819396687585133/329375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1514702867/100000000000000 : ℝ)*(base19) + (1764479463/100000000000000 : ℝ)*(base23) + (12155179/10000000000000 : ℝ)*(upper3) + (20018997/50000000000000 : ℝ)*(upper4) + (274832119/100000000000000 : ℝ)*(upper5) + (1396004503622091/100000000000000 : ℝ)*(major0) + (1396004503622091/100000000000000 : ℝ)*(major1) + (1396004503622091/100000000000000 : ℝ)*(major2) + (480132482155701/25000000000000 : ℝ)*(sp0) + (240068108399697/12500000000000 : ℝ)*(sp1) + (1920544617420979/100000000000000 : ℝ)*(sp2) + (34858262558553/4000000000000 : ℝ)*(sp3) + (8226638819/50000000000000 : ℝ)*(sp4) + (5817309619/100000000000000 : ℝ)*(sp7) + (217865595318361/25000000000000 : ℝ)*(f.failure) + (960273190950221/50000000000000 : ℝ)*(f.sum) + (24736870833439/13175000000000000000000000000 : ℝ)*base65 + (1095074550806913289/658750000000000000000000000000000 : ℝ)*base68 + (852002737063086711/658750000000000000000000000000000 : ℝ)*base69 + (1826510936216913289/658750000000000000000000000000000 : ℝ)*base72 + (6328995016911/13175000000000000000000000000 : ℝ)*base74 + (5789214790584413289/658750000000000000000000000000000 : ℝ)*base76 + (1429829664163163289/658750000000000000000000000000000 : ℝ)*base78 + (4568003959526836711/658750000000000000000000000000000 : ℝ)*base79 + (51135343476589/13175000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (15726697/2500000000000000000000 : ℝ)*base90 + (15726697/2500000000000000000000 : ℝ)*base92 + (15726697/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136910598697519504499319/13175000000000000000000000000 : ℝ) := by norm_num
    linear_combination (494118901/25000000000000 : ℝ)*(base19) + (213613363/10000000000000 : ℝ)*(base23) + (132927997/50000000000000 : ℝ)*(upper3) + (57668479/100000000000000 : ℝ)*(lower4) + (230625347/100000000000000 : ℝ)*(upper5) + (357530952701499/25000000000000 : ℝ)*(major0) + (357530952701499/25000000000000 : ℝ)*(major1) + (357530952701499/25000000000000 : ℝ)*(major2) + (2370173921/20000000000000 : ℝ)*(sp1) + (1299772303/10000000000000 : ℝ)*(sp2) + (1967485755866561/100000000000000 : ℝ)*(sp4) + (245933991065169/12500000000000 : ℝ)*(sp5) + (1967470622009901/100000000000000 : ℝ)*(sp6) + (223190379838887/25000000000000 : ℝ)*(sp7) + (223190379838887/25000000000000 : ℝ)*(f.failure) + (1967485755866561/100000000000000 : ℝ)*(f.sum) + (17641555969917/6587500000000000000000000000 : ℝ)*base65 + (249274335814768179/164687500000000000000000000000000 : ℝ)*base67 + (989249602614606821/164687500000000000000000000000000 : ℝ)*base70 + (391307195387268179/164687500000000000000000000000000 : ℝ)*base71 + (76757943838259/13175000000000000000000000000 : ℝ)*base73 + (1015637703561794321/164687500000000000000000000000000 : ℝ)*base76 + (461318640784768179/164687500000000000000000000000000 : ℝ)*base77 + (777099699525544321/164687500000000000000000000000000 : ℝ)*base80 + (393442428517/6587500000000000000000000000 : ℝ)*base81 + (16288599/2500000000000000000000 : ℝ)*base90 + (16288599/2500000000000000000000 : ℝ)*base92 + (16288599/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1472_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6503/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2297/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3893/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18793/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1472_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1472_s2_0 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-120200747/625000000 : ℝ)*x 0 + (43775419/80000000 : ℝ)*x 1 + (5185550149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (120200747/625000000 : ℝ)^4441 ≤ (733408260661/6250000000000 : ℝ)^3417 := by
    have hnat : (120200747 : ℕ)^4441*6250000000000^3417 ≤ 733408260661^3417*625000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120200747 625000000 733408260661 6250000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43775419/80000000 : ℝ)^4441 ≤ (22836877601777/50000000000000 : ℝ)^3417 := by
    have hnat : (43775419 : ℕ)^4441*50000000000000^3417 ≤ 22836877601777^3417*80000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43775419 80000000 22836877601777 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185550149/10000000000 : ℝ)^4441 ≤ (5323964076853/12500000000000 : ℝ)^3417 := by
    have hnat : (5185550149 : ℕ)^4441*12500000000000^3417 ≤ 5323964076853^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185550149 10000000000 5323964076853 12500000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-120200747/625000000 : ℝ), (43775419/80000000 : ℝ), (5185550149/10000000000 : ℝ)] ![(733408260661/6250000000000 : ℝ), (22836877601777/50000000000000 : ℝ), (5323964076853/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-120200747/625000000 : ℝ)|^4441 ≤ (733408260661/6250000000000 : ℝ)^3417
        have hw : |(-120200747/625000000 : ℝ)|=(120200747/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43775419/80000000 : ℝ)|^4441 ≤ (22836877601777/50000000000000 : ℝ)^3417
        have hw : |(43775419/80000000 : ℝ)|=(43775419/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185550149/10000000000 : ℝ)|^4441 ≤ (5323964076853/12500000000000 : ℝ)^3417
        have hw : |(5185550149/10000000000 : ℝ)|=(5185550149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s2_1 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268116223/500000000 : ℝ)*x 0 + (-517755709/2500000000 : ℝ)*x 1 + (5185551437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268116223/500000000 : ℝ)^4441 ≤ (17795333559/40000000000 : ℝ)^3417 := by
    have hnat : (268116223 : ℕ)^4441*40000000000^3417 ≤ 17795333559^3417*500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268116223 500000000 17795333559 40000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517755709/2500000000 : ℝ)^4441 ≤ (12919939725057/100000000000000 : ℝ)^3417 := by
    have hnat : (517755709 : ℕ)^4441*100000000000000^3417 ≤ 12919939725057^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517755709 2500000000 12919939725057 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185551437/10000000000 : ℝ)^4441 ≤ (42591726364167/100000000000000 : ℝ)^3417 := by
    have hnat : (5185551437 : ℕ)^4441*100000000000000^3417 ≤ 42591726364167^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185551437 10000000000 42591726364167 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268116223/500000000 : ℝ), (-517755709/2500000000 : ℝ), (5185551437/10000000000 : ℝ)] ![(17795333559/40000000000 : ℝ), (12919939725057/100000000000000 : ℝ), (42591726364167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268116223/500000000 : ℝ)|^4441 ≤ (17795333559/40000000000 : ℝ)^3417
        have hw : |(268116223/500000000 : ℝ)|=(268116223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-517755709/2500000000 : ℝ)|^4441 ≤ (12919939725057/100000000000000 : ℝ)^3417
        have hw : |(-517755709/2500000000 : ℝ)|=(517755709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185551437/10000000000 : ℝ)|^4441 ≤ (42591726364167/100000000000000 : ℝ)^3417
        have hw : |(5185551437/10000000000 : ℝ)|=(5185551437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s2_2 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362325243/10000000000 : ℝ)*x 0 + (5185550819/10000000000 : ℝ)*x 1 + (-129438913/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362325243/10000000000 : ℝ)^4441 ≤ (2224417117019/5000000000000 : ℝ)^3417 := by
    have hnat : (5362325243 : ℕ)^4441*5000000000000^3417 ≤ 2224417117019^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362325243 10000000000 2224417117019 5000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185550819/10000000000 : ℝ)^4441 ≤ (10647929941761/25000000000000 : ℝ)^3417 := by
    have hnat : (5185550819 : ℕ)^4441*25000000000000^3417 ≤ 10647929941761^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185550819 10000000000 10647929941761 25000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129438913/625000000 : ℝ)^4441 ≤ (12919937876443/100000000000000 : ℝ)^3417 := by
    have hnat : (129438913 : ℕ)^4441*100000000000000^3417 ≤ 12919937876443^3417*625000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129438913 625000000 12919937876443 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362325243/10000000000 : ℝ), (5185550819/10000000000 : ℝ), (-129438913/625000000 : ℝ)] ![(2224417117019/5000000000000 : ℝ), (10647929941761/25000000000000 : ℝ), (12919937876443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362325243/10000000000 : ℝ)|^4441 ≤ (2224417117019/5000000000000 : ℝ)^3417
        have hw : |(5362325243/10000000000 : ℝ)|=(5362325243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185550819/10000000000 : ℝ)|^4441 ≤ (10647929941761/25000000000000 : ℝ)^3417
        have hw : |(5185550819/10000000000 : ℝ)|=(5185550819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129438913/625000000 : ℝ)|^4441 ≤ (12919937876443/100000000000000 : ℝ)^3417
        have hw : |(-129438913/625000000 : ℝ)|=(129438913/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s2_3 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2142596069/5000000000 : ℝ)*x 0 + (994955143/2500000000 : ℝ)*x 1 + (72045991/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142596069/5000000000 : ℝ)^4441 ≤ (33241442788033/100000000000000 : ℝ)^3417 := by
    have hnat : (2142596069 : ℕ)^4441*100000000000000^3417 ≤ 33241442788033^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142596069 5000000000 33241442788033 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994955143/2500000000 : ℝ)^4441 ≤ (6039226915189/20000000000000 : ℝ)^3417 := by
    have hnat : (994955143 : ℕ)^4441*20000000000000^3417 ≤ 6039226915189^3417*2500000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994955143 2500000000 6039226915189 20000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (72045991/156250000 : ℝ)^4441 ≤ (36562422616809/100000000000000 : ℝ)^3417 := by
    have hnat : (72045991 : ℕ)^4441*100000000000000^3417 ≤ 36562422616809^3417*156250000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72045991 156250000 36562422616809 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2142596069/5000000000 : ℝ), (994955143/2500000000 : ℝ), (72045991/156250000 : ℝ)] ![(33241442788033/100000000000000 : ℝ), (6039226915189/20000000000000 : ℝ), (36562422616809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2142596069/5000000000 : ℝ)|^4441 ≤ (33241442788033/100000000000000 : ℝ)^3417
        have hw : |(2142596069/5000000000 : ℝ)|=(2142596069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(994955143/2500000000 : ℝ)|^4441 ≤ (6039226915189/20000000000000 : ℝ)^3417
        have hw : |(994955143/2500000000 : ℝ)|=(994955143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(72045991/156250000 : ℝ)|^4441 ≤ (36562422616809/100000000000000 : ℝ)^3417
        have hw : |(72045991/156250000 : ℝ)|=(72045991/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s2_4 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1923276483/10000000000 : ℝ)*x 0 + (81053503/156250000 : ℝ)*x 1 + (547003591/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1923276483/10000000000 : ℝ)^4441 ≤ (11735043905437/100000000000000 : ℝ)^3417 := by
    have hnat : (1923276483 : ℕ)^4441*100000000000000^3417 ≤ 11735043905437^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923276483 10000000000 11735043905437 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81053503/156250000 : ℝ)^4441 ≤ (10652929755757/25000000000000 : ℝ)^3417 := by
    have hnat : (81053503 : ℕ)^4441*25000000000000^3417 ≤ 10652929755757^3417*156250000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81053503 156250000 10652929755757 25000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547003591/1000000000 : ℝ)^4441 ≤ (45653237062901/100000000000000 : ℝ)^3417 := by
    have hnat : (547003591 : ℕ)^4441*100000000000000^3417 ≤ 45653237062901^3417*1000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547003591 1000000000 45653237062901 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1923276483/10000000000 : ℝ), (81053503/156250000 : ℝ), (547003591/1000000000 : ℝ)] ![(11735043905437/100000000000000 : ℝ), (10652929755757/25000000000000 : ℝ), (45653237062901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1923276483/10000000000 : ℝ)|^4441 ≤ (11735043905437/100000000000000 : ℝ)^3417
        have hw : |(-1923276483/10000000000 : ℝ)|=(1923276483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81053503/156250000 : ℝ)|^4441 ≤ (10652929755757/25000000000000 : ℝ)^3417
        have hw : |(81053503/156250000 : ℝ)|=(81053503/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547003591/1000000000 : ℝ)|^4441 ≤ (45653237062901/100000000000000 : ℝ)^3417
        have hw : |(547003591/1000000000 : ℝ)|=(547003591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s2_5 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20654699/39062500 : ℝ)*x 0 + (-893269011/5000000000 : ℝ)*x 1 + (68375449/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20654699/39062500 : ℝ)^4441 ≤ (21842159754621/50000000000000 : ℝ)^3417 := by
    have hnat : (20654699 : ℕ)^4441*50000000000000^3417 ≤ 21842159754621^3417*39062500^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20654699 39062500 21842159754621 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (893269011/5000000000 : ℝ)^4441 ≤ (2132488659581/20000000000000 : ℝ)^3417 := by
    have hnat : (893269011 : ℕ)^4441*20000000000000^3417 ≤ 2132488659581^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893269011 5000000000 2132488659581 20000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68375449/125000000 : ℝ)^4441 ≤ (11413309292843/25000000000000 : ℝ)^3417 := by
    have hnat : (68375449 : ℕ)^4441*25000000000000^3417 ≤ 11413309292843^3417*125000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68375449 125000000 11413309292843 25000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20654699/39062500 : ℝ), (-893269011/5000000000 : ℝ), (68375449/125000000 : ℝ)] ![(21842159754621/50000000000000 : ℝ), (2132488659581/20000000000000 : ℝ), (11413309292843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20654699/39062500 : ℝ)|^4441 ≤ (21842159754621/50000000000000 : ℝ)^3417
        have hw : |(20654699/39062500 : ℝ)|=(20654699/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-893269011/5000000000 : ℝ)|^4441 ≤ (2132488659581/20000000000000 : ℝ)^3417
        have hw : |(-893269011/5000000000 : ℝ)|=(893269011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68375449/125000000 : ℝ)|^4441 ≤ (11413309292843/25000000000000 : ℝ)^3417
        have hw : |(68375449/125000000 : ℝ)|=(68375449/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s2_6 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287603063/10000000000 : ℝ)*x 0 + (683754493/1250000000 : ℝ)*x 1 + (-71461513/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287603063/10000000000 : ℝ)^4441 ≤ (21842160393501/50000000000000 : ℝ)^3417 := by
    have hnat : (5287603063 : ℕ)^4441*50000000000000^3417 ≤ 21842160393501^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287603063 10000000000 21842160393501 50000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683754493/1250000000 : ℝ)^4441 ≤ (9130647486341/20000000000000 : ℝ)^3417 := by
    have hnat : (683754493 : ℕ)^4441*20000000000000^3417 ≤ 9130647486341^3417*1250000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683754493 1250000000 9130647486341 20000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71461513/400000000 : ℝ)^4441 ≤ (10662441769823/100000000000000 : ℝ)^3417 := by
    have hnat : (71461513 : ℕ)^4441*100000000000000^3417 ≤ 10662441769823^3417*400000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71461513 400000000 10662441769823 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287603063/10000000000 : ℝ), (683754493/1250000000 : ℝ), (-71461513/400000000 : ℝ)] ![(21842160393501/50000000000000 : ℝ), (9130647486341/20000000000000 : ℝ), (10662441769823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287603063/10000000000 : ℝ)|^4441 ≤ (21842160393501/50000000000000 : ℝ)^3417
        have hw : |(5287603063/10000000000 : ℝ)|=(5287603063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683754493/1250000000 : ℝ)|^4441 ≤ (9130647486341/20000000000000 : ℝ)^3417
        have hw : |(683754493/1250000000 : ℝ)|=(683754493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-71461513/400000000 : ℝ)|^4441 ≤ (10662441769823/100000000000000 : ℝ)^3417
        have hw : |(-71461513/400000000 : ℝ)|=(71461513/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1472_s2_7 (p : ℝ) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2142667881/5000000000 : ℝ)*x 0 + (921362743/2000000000 : ℝ)*x 1 + (3983988451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142667881/5000000000 : ℝ)^4441 ≤ (33242890808029/100000000000000 : ℝ)^3417 := by
    have hnat : (2142667881 : ℕ)^4441*100000000000000^3417 ≤ 33242890808029^3417*5000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142667881 5000000000 33242890808029 100000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (921362743/2000000000 : ℝ)^4441 ≤ (7303973689511/20000000000000 : ℝ)^3417 := by
    have hnat : (921362743 : ℕ)^4441*20000000000000^3417 ≤ 7303973689511^3417*2000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921362743 2000000000 7303973689511 20000000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3983988451/10000000000 : ℝ)^4441 ≤ (3779655091699/12500000000000 : ℝ)^3417 := by
    have hnat : (3983988451 : ℕ)^4441*12500000000000^3417 ≤ 3779655091699^3417*10000000000^4441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3983988451 10000000000 3779655091699 12500000000000 4441 3417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4441/1024 : ℝ)) 4441 3417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2142667881/5000000000 : ℝ), (921362743/2000000000 : ℝ), (3983988451/10000000000 : ℝ)] ![(33242890808029/100000000000000 : ℝ), (7303973689511/20000000000000 : ℝ), (3779655091699/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2142667881/5000000000 : ℝ)|^4441 ≤ (33242890808029/100000000000000 : ℝ)^3417
        have hw : |(2142667881/5000000000 : ℝ)|=(2142667881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(921362743/2000000000 : ℝ)|^4441 ≤ (7303973689511/20000000000000 : ℝ)^3417
        have hw : |(921362743/2000000000 : ℝ)|=(921362743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3983988451/10000000000 : ℝ)|^4441 ≤ (3779655091699/12500000000000 : ℝ)^3417
        have hw : |(3983988451/10000000000 : ℝ)|=(3983988451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1472_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18793/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3893/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10113/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16169/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18793/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3893/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18793/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3893/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18793/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3893/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18793/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3893/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18793/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3893/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18793/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3893/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3893/50000 : ℝ) ^ (4439/1024 : ℝ) ≤ (1562756195597809/100000000000000000000 : ℝ) := by
    have hpowers : (3893/50000 : ℝ)^4439 ≤ (1562756195597809/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3893 : ℕ)^4439*100000000000000000000^1024 ≤ 1562756195597809^1024*50000^4439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3893 50000 1562756195597809 100000000000000000000 4439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3893/50000 : ℝ)) (X := (1562756195597809/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18793/100000 : ℝ) ^ (4439/1024 : ℝ) ≤ (14250546130451193/20000000000000000000 : ℝ) := by
    have hpowers : (18793/100000 : ℝ)^4439 ≤ (14250546130451193/20000000000000000000 : ℝ)^1024 := by
      have hnat : (18793 : ℕ)^4439*20000000000000000000^1024 ≤ 14250546130451193^1024*100000^4439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18793 100000 14250546130451193 20000000000000000000 4439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18793/100000 : ℝ)) (X := (14250546130451193/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001562756195597809/50000000000000000000 : ℝ) ≤ (10000072099261339/10000000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (50001562756195597809/50000000000000000000 : ℝ)^1024 ≤ (10000072099261339/10000000000000000 : ℝ)^4439 := by
      have hnat : (50001562756195597809 : ℕ)^1024*10000000000000000^4439 ≤ 10000072099261339^4439*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001562756195597809 50000000000000000000 10000072099261339 10000000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000072099261339/10000000000000000 : ℝ)) (X := (50001562756195597809/50000000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50036407743423926887/50000000000000000000 : ℝ) ≤ (10001679256207403/10000000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (50036407743423926887/50000000000000000000 : ℝ)^1024 ≤ (10001679256207403/10000000000000000 : ℝ)^4439 := by
      have hnat : (50036407743423926887 : ℕ)^1024*10000000000000000^4439 ≤ 10001679256207403^4439*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036407743423926887 50000000000000000000 10001679256207403 10000000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001679256207403/10000000000000000 : ℝ)) (X := (50036407743423926887/50000000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10014250546130451193/10000000000000000000 : ℝ) ≤ (10003286413153467/10000000000000000 : ℝ) ^ (4439/1024 : ℝ) := by
    have hpowers : (10014250546130451193/10000000000000000000 : ℝ)^1024 ≤ (10003286413153467/10000000000000000 : ℝ)^4439 := by
      have hnat : (10014250546130451193 : ℕ)^1024*10000000000000000^4439 ≤ 10003286413153467^4439*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10014250546130451193 10000000000000000000 10003286413153467 10000000000000000 1024 4439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003286413153467/10000000000000000 : ℝ)) (X := (10014250546130451193/10000000000000000000 : ℝ)) (by norm_num) 4439 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1562756195597809/100000000000000000000 : ℝ) ≤ ((22009153389721089953/22014000000000000000 : ℝ)+2*(100447309129/68793750000000 : ℝ)*(3893/50000 : ℝ))^(4439/1024 : ℝ) := by
    rw [show (22009153389721089953/22014000000000000000 : ℝ)+2*(100447309129/68793750000000 : ℝ)*(3893/50000 : ℝ)=(10000072099261339/10000000000000000 : ℝ) by norm_num, show 1+2*(1562756195597809/100000000000000000000 : ℝ)=(50001562756195597809/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14250546130451193/20000000000000000000 : ℝ)+(1562756195597809/100000000000000000000 : ℝ) ≤ ((22009153389721089953/22014000000000000000 : ℝ)+(100447309129/68793750000000 : ℝ)*((18793/100000 : ℝ)+(3893/50000 : ℝ)))^(4439/1024 : ℝ) := by
    rw [show (22009153389721089953/22014000000000000000 : ℝ)+(100447309129/68793750000000 : ℝ)*((18793/100000 : ℝ)+(3893/50000 : ℝ))=(10001679256207403/10000000000000000 : ℝ) by norm_num, show 1+(14250546130451193/20000000000000000000 : ℝ)+(1562756195597809/100000000000000000000 : ℝ)=(50036407743423926887/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14250546130451193/20000000000000000000 : ℝ) ≤ ((22009153389721089953/22014000000000000000 : ℝ)+2*(100447309129/68793750000000 : ℝ)*(18793/100000 : ℝ))^(4439/1024 : ℝ) := by
    rw [show (22009153389721089953/22014000000000000000 : ℝ)+2*(100447309129/68793750000000 : ℝ)*(18793/100000 : ℝ)=(10003286413153467/10000000000000000 : ℝ) by norm_num, show 1+2*(14250546130451193/20000000000000000000 : ℝ)=(10014250546130451193/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22009153389721089953/22014000000000000000 : ℝ)*(X 1 0+X 2 0)+(100447309129/68793750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (3893/50000 : ℝ)) (hi := (18793/100000 : ℝ)) (c := (22009153389721089953/22014000000000000000 : ℝ)) (alpha := (100447309129/68793750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22009153389721089953/22014000000000000000 : ℝ)*(X 0 1+X 2 1)+(100447309129/68793750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (3893/50000 : ℝ)) (hi := (18793/100000 : ℝ)) (c := (22009153389721089953/22014000000000000000 : ℝ)) (alpha := (100447309129/68793750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22009153389721089953/22014000000000000000 : ℝ)*(X 0 2+X 1 2)+(100447309129/68793750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4439/1024 : ℝ)) (lo := (3893/50000 : ℝ)) (hi := (18793/100000 : ℝ)) (c := (22009153389721089953/22014000000000000000 : ℝ)) (alpha := (100447309129/68793750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-120200747/625000000 : ℝ)*X 0 0+(43775419/80000000 : ℝ)*X 0 1+(5185550149/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((268116223/500000000 : ℝ)*X 1 0+(-517755709/2500000000 : ℝ)*X 1 1+(5185551437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5362325243/10000000000 : ℝ)*X 2 0+(5185550819/10000000000 : ℝ)*X 2 1+(-129438913/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2142596069/5000000000 : ℝ)*X 0 0+(994955143/2500000000 : ℝ)*X 0 1+(72045991/156250000 : ℝ)*X 0 2+(2142596069/5000000000 : ℝ)*X 1 0+(994955143/2500000000 : ℝ)*X 1 1+(72045991/156250000 : ℝ)*X 1 2+(2142596069/5000000000 : ℝ)*X 2 0+(994955143/2500000000 : ℝ)*X 2 1+(72045991/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1923276483/10000000000 : ℝ)*X 0 0+(81053503/156250000 : ℝ)*X 0 1+(547003591/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((20654699/39062500 : ℝ)*X 1 0+(-893269011/5000000000 : ℝ)*X 1 1+(68375449/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287603063/10000000000 : ℝ)*X 2 0+(683754493/1250000000 : ℝ)*X 2 1+(-71461513/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2142667881/5000000000 : ℝ)*X 0 0+(921362743/2000000000 : ℝ)*X 0 1+(3983988451/10000000000 : ℝ)*X 0 2+(2142667881/5000000000 : ℝ)*X 1 0+(921362743/2000000000 : ℝ)*X 1 1+(3983988451/10000000000 : ℝ)*X 1 2+(2142667881/5000000000 : ℝ)*X 2 0+(921362743/2000000000 : ℝ)*X 2 1+(3983988451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1472_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (697671071591760775692256719/122300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21864453/2500000000000 : ℝ)*(base19) + (516908109/50000000000000 : ℝ)*(base23) + (11657819/10000000000000 : ℝ)*(upper3) + (94015297/50000000000000 : ℝ)*(upper4) + (127406941/100000000000000 : ℝ)*(upper5) + (2538220866037869/100000000000000 : ℝ)*(major0) + (2538220866037869/100000000000000 : ℝ)*(major1) + (253822086603787/10000000000000 : ℝ)*(major2) + (3491918708311669/100000000000000 : ℝ)*(sp0) + (1745972173162793/50000000000000 : ℝ)*(sp1) + (27280813961621/781250000000 : ℝ)*(sp2) + (792243034792457/50000000000000 : ℝ)*(sp3) + (26512592037/100000000000000 : ℝ)*(sp4) + (640714637/6250000000000 : ℝ)*(sp7) + (792248160509553/50000000000000 : ℝ)*(f.failure) + (1745972610451853/50000000000000 : ℝ)*(f.sum) + (283841003601953/55035000000000000000000000000 : ℝ)*base65 + (17985246200166769843/2201400000000000000000000000000000 : ℝ)*base68 + (175029597014375989/220140000000000000000000000000000 : ℝ)*base70 + (10181618525332630157/2201400000000000000000000000000000 : ℝ)*base71 + (30563013189509/6879375000000000000000000000 : ℝ)*base74 + (736189360003284011/220140000000000000000000000000000 : ℝ)*base75 + (4409963394274083281/733800000000000000000000000000000 : ℝ)*base78 + (2798837060086083281/733800000000000000000000000000000 : ℝ)*base80 + (57420170693/71660156250000000000000000 : ℝ)*base82 + (46342719/5000000000000000000000 : ℝ)*base89 + (46342719/5000000000000000000000 : ℝ)*base91 + (3657281/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30674060228174430834433/6115000000000000000000000000 : ℝ) := by norm_num
    linear_combination (327574867/50000000000000 : ℝ)*(base19) + (166886973/20000000000000 : ℝ)*(base23) + (9155701/10000000000000 : ℝ)*(upper3) + (30861273/100000000000000 : ℝ)*(lower4) + (119656219/100000000000000 : ℝ)*(upper5) + (2572005618322089/100000000000000 : ℝ)*(major0) + (2572005618322089/100000000000000 : ℝ)*(major1) + (2572005618322089/100000000000000 : ℝ)*(major2) + (7338252237/100000000000000 : ℝ)*(sp1) + (5129860851/50000000000000 : ℝ)*(sp2) + (1769212228903461/50000000000000 : ℝ)*(sp4) + (442302058050619/12500000000000 : ℝ)*(sp5) + (884603340912589/25000000000000 : ℝ)*(sp6) + (401396652907649/25000000000000 : ℝ)*(sp7) + (401396652907649/25000000000000 : ℝ)*(f.failure) + (1769212228903461/50000000000000 : ℝ)*(f.sum) + (46914717696869/9172500000000000000000000000 : ℝ)*base66 + (3071711977940063939/733800000000000000000000000000000 : ℝ)*base67 + (6741713870302463939/733800000000000000000000000000000 : ℝ)*base69 + (2776005307184736061/733800000000000000000000000000000 : ℝ)*base72 + (3581836890019/2293125000000000000000000000 : ℝ)*base73 + (6703792604945736061/733800000000000000000000000000000 : ℝ)*base76 + (1246709549872463939/733800000000000000000000000000000 : ℝ)*base77 + (7523415605316336061/733800000000000000000000000000000 : ℝ)*base80 + (11871398424079/2293125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7165073/2500000000000000000000 : ℝ)*base90 + (7165073/2500000000000000000000 : ℝ)*base92 + (7165073/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1472_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18793/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3893/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10113/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1472_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1472_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10113/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1472_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1472_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1472_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4439/1024 : ℝ) ≤ p) (hpb : p ≤ (4441/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160191023/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10113/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16169/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1472_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

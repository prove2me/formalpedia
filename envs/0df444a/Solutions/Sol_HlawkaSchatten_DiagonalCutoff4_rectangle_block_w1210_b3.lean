-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1210_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:07:07.772444+00:00
-- url     : https://prove2.me/submissions/6841967d-f9bf-411f-81b0-e9b42063838c

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
theorem support_rectangle_w1210_box_0 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-402017153/2000000000 : ℝ)*x 0 + (1343830707/2500000000 : ℝ)*x 1 + (1075064513/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402017153/2000000000 : ℝ)^8403 ≤ (2996431791809/25000000000000 : ℝ)^6355 := by
    have hnat : (402017153 : ℕ)^8403*25000000000000^6355 ≤ 2996431791809^6355*2000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402017153 2000000000 2996431791809 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343830707/2500000000 : ℝ)^8403 ≤ (22003568918053/50000000000000 : ℝ)^6355 := by
    have hnat : (1343830707 : ℕ)^8403*50000000000000^6355 ≤ 22003568918053^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343830707 2500000000 22003568918053 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075064513/2000000000 : ℝ)^8403 ≤ (44007134989069/100000000000000 : ℝ)^6355 := by
    have hnat : (1075064513 : ℕ)^8403*100000000000000^6355 ≤ 44007134989069^6355*2000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075064513 2000000000 44007134989069 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-402017153/2000000000 : ℝ), (1343830707/2500000000 : ℝ), (1075064513/2000000000 : ℝ)] ![(2996431791809/25000000000000 : ℝ), (22003568918053/50000000000000 : ℝ), (44007134989069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-402017153/2000000000 : ℝ)|^8403 ≤ (2996431791809/25000000000000 : ℝ)^6355
        have hw : |(-402017153/2000000000 : ℝ)|=(402017153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1343830707/2500000000 : ℝ)|^8403 ≤ (22003568918053/50000000000000 : ℝ)^6355
        have hw : |(1343830707/2500000000 : ℝ)|=(1343830707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075064513/2000000000 : ℝ)|^8403 ≤ (44007134989069/100000000000000 : ℝ)^6355
        have hw : |(1075064513/2000000000 : ℝ)|=(1075064513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_box_1 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2648280177/5000000000 : ℝ)*x 0 + (-13231649/62500000 : ℝ)*x 1 + (2687661129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648280177/5000000000 : ℝ)^8403 ≤ (21578267607193/50000000000000 : ℝ)^6355 := by
    have hnat : (2648280177 : ℕ)^8403*50000000000000^6355 ≤ 21578267607193^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648280177 5000000000 21578267607193 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13231649/62500000 : ℝ)^8403 ≤ (3209083275713/25000000000000 : ℝ)^6355 := by
    have hnat : (13231649 : ℕ)^8403*25000000000000^6355 ≤ 3209083275713^6355*62500000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13231649 62500000 3209083275713 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687661129/5000000000 : ℝ)^8403 ≤ (44007131665721/100000000000000 : ℝ)^6355 := by
    have hnat : (2687661129 : ℕ)^8403*100000000000000^6355 ≤ 44007131665721^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687661129 5000000000 44007131665721 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648280177/5000000000 : ℝ), (-13231649/62500000 : ℝ), (2687661129/5000000000 : ℝ)] ![(21578267607193/50000000000000 : ℝ), (3209083275713/25000000000000 : ℝ), (44007131665721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648280177/5000000000 : ℝ)|^8403 ≤ (21578267607193/50000000000000 : ℝ)^6355
        have hw : |(2648280177/5000000000 : ℝ)|=(2648280177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13231649/62500000 : ℝ)|^8403 ≤ (3209083275713/25000000000000 : ℝ)^6355
        have hw : |(-13231649/62500000 : ℝ)|=(13231649/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687661129/5000000000 : ℝ)|^8403 ≤ (44007131665721/100000000000000 : ℝ)^6355
        have hw : |(2687661129/5000000000 : ℝ)|=(2687661129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_box_2 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296561053/10000000000 : ℝ)*x 0 + (537532227/1000000000 : ℝ)*x 1 + (-529265721/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296561053/10000000000 : ℝ)^8403 ≤ (43156542745317/100000000000000 : ℝ)^6355 := by
    have hnat : (5296561053 : ℕ)^8403*100000000000000^6355 ≤ 43156542745317^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296561053 10000000000 43156542745317 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537532227/1000000000 : ℝ)^8403 ≤ (5500891474453/12500000000000 : ℝ)^6355 := by
    have hnat : (537532227 : ℕ)^8403*12500000000000^6355 ≤ 5500891474453^6355*1000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537532227 1000000000 5500891474453 12500000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529265721/2500000000 : ℝ)^8403 ≤ (6418162719177/50000000000000 : ℝ)^6355 := by
    have hnat : (529265721 : ℕ)^8403*50000000000000^6355 ≤ 6418162719177^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529265721 2500000000 6418162719177 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296561053/10000000000 : ℝ), (537532227/1000000000 : ℝ), (-529265721/2500000000 : ℝ)] ![(43156542745317/100000000000000 : ℝ), (5500891474453/12500000000000 : ℝ), (6418162719177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296561053/10000000000 : ℝ)|^8403 ≤ (43156542745317/100000000000000 : ℝ)^6355
        have hw : |(5296561053/10000000000 : ℝ)|=(5296561053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537532227/1000000000 : ℝ)|^8403 ≤ (5500891474453/12500000000000 : ℝ)^6355
        have hw : |(537532227/1000000000 : ℝ)|=(537532227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-529265721/2500000000 : ℝ)|^8403 ≤ (6418162719177/50000000000000 : ℝ)^6355
        have hw : |(-529265721/2500000000 : ℝ)|=(529265721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_box_3 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4462028599/10000000000 : ℝ)*x 0 + (4303821567/10000000000 : ℝ)*x 1 + (4303822889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4462028599/10000000000 : ℝ)^8403 ≤ (1376095443183/4000000000000 : ℝ)^6355 := by
    have hnat : (4462028599 : ℕ)^8403*4000000000000^6355 ≤ 1376095443183^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4462028599 10000000000 1376095443183 4000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4303821567/10000000000 : ℝ)^8403 ≤ (32798800291731/100000000000000 : ℝ)^6355 := by
    have hnat : (4303821567 : ℕ)^8403*100000000000000^6355 ≤ 32798800291731^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303821567 10000000000 32798800291731 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4303822889/10000000000 : ℝ)^8403 ≤ (16399406806629/50000000000000 : ℝ)^6355 := by
    have hnat : (4303822889 : ℕ)^8403*50000000000000^6355 ≤ 16399406806629^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303822889 10000000000 16399406806629 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4462028599/10000000000 : ℝ), (4303821567/10000000000 : ℝ), (4303822889/10000000000 : ℝ)] ![(1376095443183/4000000000000 : ℝ), (32798800291731/100000000000000 : ℝ), (16399406806629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4462028599/10000000000 : ℝ)|^8403 ≤ (1376095443183/4000000000000 : ℝ)^6355
        have hw : |(4462028599/10000000000 : ℝ)|=(4462028599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4303821567/10000000000 : ℝ)|^8403 ≤ (32798800291731/100000000000000 : ℝ)^6355
        have hw : |(4303821567/10000000000 : ℝ)|=(4303821567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4303822889/10000000000 : ℝ)|^8403 ≤ (16399406806629/50000000000000 : ℝ)^6355
        have hw : |(4303822889/10000000000 : ℝ)|=(4303822889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_box_4 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-282608853/1250000000 : ℝ)*x 0 + (2640972847/5000000000 : ℝ)*x 1 + (5281945733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (282608853/1250000000 : ℝ)^8403 ≤ (2800340345213/20000000000000 : ℝ)^6355 := by
    have hnat : (282608853 : ℕ)^8403*20000000000000^6355 ≤ 2800340345213^6355*1250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282608853 1250000000 2800340345213 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640972847/5000000000 : ℝ)^8403 ≤ (42999148918321/100000000000000 : ℝ)^6355 := by
    have hnat : (2640972847 : ℕ)^8403*100000000000000^6355 ≤ 42999148918321^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640972847 5000000000 42999148918321 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281945733/10000000000 : ℝ)^8403 ≤ (2687446833633/6250000000000 : ℝ)^6355 := by
    have hnat : (5281945733 : ℕ)^8403*6250000000000^6355 ≤ 2687446833633^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281945733 10000000000 2687446833633 6250000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-282608853/1250000000 : ℝ), (2640972847/5000000000 : ℝ), (5281945733/10000000000 : ℝ)] ![(2800340345213/20000000000000 : ℝ), (42999148918321/100000000000000 : ℝ), (2687446833633/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-282608853/1250000000 : ℝ)|^8403 ≤ (2800340345213/20000000000000 : ℝ)^6355
        have hw : |(-282608853/1250000000 : ℝ)|=(282608853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640972847/5000000000 : ℝ)|^8403 ≤ (42999148918321/100000000000000 : ℝ)^6355
        have hw : |(2640972847/5000000000 : ℝ)|=(2640972847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281945733/10000000000 : ℝ)|^8403 ≤ (2687446833633/6250000000000 : ℝ)^6355
        have hw : |(5281945733/10000000000 : ℝ)|=(5281945733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_box_5 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (268121559/500000000 : ℝ)*x 0 + (-430798149/2000000000 : ℝ)*x 1 + (1320486423/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268121559/500000000 : ℝ)^8403 ≤ (43867636661503/100000000000000 : ℝ)^6355 := by
    have hnat : (268121559 : ℕ)^8403*100000000000000^6355 ≤ 43867636661503^6355*500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268121559 500000000 43867636661503 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430798149/2000000000 : ℝ)^8403 ≤ (13133214428359/100000000000000 : ℝ)^6355 := by
    have hnat : (430798149 : ℕ)^8403*100000000000000^6355 ≤ 13133214428359^6355*2000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430798149 2000000000 13133214428359 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320486423/2500000000 : ℝ)^8403 ≤ (5374893612099/12500000000000 : ℝ)^6355 := by
    have hnat : (1320486423 : ℕ)^8403*12500000000000^6355 ≤ 5374893612099^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320486423 2500000000 5374893612099 12500000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268121559/500000000 : ℝ), (-430798149/2000000000 : ℝ), (1320486423/2500000000 : ℝ)] ![(43867636661503/100000000000000 : ℝ), (13133214428359/100000000000000 : ℝ), (5374893612099/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268121559/500000000 : ℝ)|^8403 ≤ (43867636661503/100000000000000 : ℝ)^6355
        have hw : |(268121559/500000000 : ℝ)|=(268121559/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430798149/2000000000 : ℝ)|^8403 ≤ (13133214428359/100000000000000 : ℝ)^6355
        have hw : |(-430798149/2000000000 : ℝ)|=(430798149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320486423/2500000000 : ℝ)|^8403 ≤ (5374893612099/12500000000000 : ℝ)^6355
        have hw : |(1320486423/2500000000 : ℝ)|=(1320486423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_box_6 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (67030389/125000000 : ℝ)*x 0 + (528194573/1000000000 : ℝ)*x 1 + (-86159631/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67030389/125000000 : ℝ)^8403 ≤ (43867636012491/100000000000000 : ℝ)^6355 := by
    have hnat : (67030389 : ℕ)^8403*100000000000000^6355 ≤ 43867636012491^6355*125000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67030389 125000000 43867636012491 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528194573/1000000000 : ℝ)^8403 ≤ (8599829861167/20000000000000 : ℝ)^6355 := by
    have hnat : (528194573 : ℕ)^8403*20000000000000^6355 ≤ 8599829861167^6355*1000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528194573 1000000000 8599829861167 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86159631/400000000 : ℝ)^8403 ≤ (13133214670221/100000000000000 : ℝ)^6355 := by
    have hnat : (86159631 : ℕ)^8403*100000000000000^6355 ≤ 13133214670221^6355*400000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86159631 400000000 13133214670221 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67030389/125000000 : ℝ), (528194573/1000000000 : ℝ), (-86159631/400000000 : ℝ)] ![(43867636012491/100000000000000 : ℝ), (8599829861167/20000000000000 : ℝ), (13133214670221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67030389/125000000 : ℝ)|^8403 ≤ (43867636012491/100000000000000 : ℝ)^6355
        have hw : |(67030389/125000000 : ℝ)|=(67030389/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528194573/1000000000 : ℝ)|^8403 ≤ (8599829861167/20000000000000 : ℝ)^6355
        have hw : |(528194573/1000000000 : ℝ)|=(528194573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86159631/400000000 : ℝ)|^8403 ≤ (13133214670221/100000000000000 : ℝ)^6355
        have hw : |(-86159631/400000000 : ℝ)|=(86159631/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_box_7 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4247947121/10000000000 : ℝ)*x 0 + (2205421323/5000000000 : ℝ)*x 1 + (2205421313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4247947121/10000000000 : ℝ)^8403 ≤ (6447389227177/20000000000000 : ℝ)^6355 := by
    have hnat : (4247947121 : ℕ)^8403*20000000000000^6355 ≤ 6447389227177^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247947121 10000000000 6447389227177 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205421323/5000000000 : ℝ)^8403 ≤ (16940763512527/50000000000000 : ℝ)^6355 := by
    have hnat : (2205421323 : ℕ)^8403*50000000000000^6355 ≤ 16940763512527^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205421323 5000000000 16940763512527 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205421313/5000000000 : ℝ)^8403 ≤ (33881526821917/100000000000000 : ℝ)^6355 := by
    have hnat : (2205421313 : ℕ)^8403*100000000000000^6355 ≤ 33881526821917^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205421313 5000000000 33881526821917 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4247947121/10000000000 : ℝ), (2205421323/5000000000 : ℝ), (2205421313/5000000000 : ℝ)] ![(6447389227177/20000000000000 : ℝ), (16940763512527/50000000000000 : ℝ), (33881526821917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4247947121/10000000000 : ℝ)|^8403 ≤ (6447389227177/20000000000000 : ℝ)^6355
        have hw : |(4247947121/10000000000 : ℝ)|=(4247947121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2205421323/5000000000 : ℝ)|^8403 ≤ (16940763512527/50000000000000 : ℝ)^6355
        have hw : |(2205421323/5000000000 : ℝ)|=(2205421323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2205421313/5000000000 : ℝ)|^8403 ≤ (33881526821917/100000000000000 : ℝ)^6355
        have hw : |(2205421313/5000000000 : ℝ)|=(2205421313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_box_8 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1104176477/5000000000 : ℝ)*x 0 + (5218312389/10000000000 : ℝ)*x 1 + (5384935387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104176477/5000000000 : ℝ)^8403 ≤ (13573258047939/100000000000000 : ℝ)^6355 := by
    have hnat : (1104176477 : ℕ)^8403*100000000000000^6355 ≤ 13573258047939^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104176477 5000000000 13573258047939 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218312389/10000000000 : ℝ)^8403 ≤ (21157757953817/50000000000000 : ℝ)^6355 := by
    have hnat : (5218312389 : ℕ)^8403*50000000000000^6355 ≤ 21157757953817^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218312389 10000000000 21157757953817 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384935387/10000000000 : ℝ)^8403 ≤ (22055613014917/50000000000000 : ℝ)^6355 := by
    have hnat : (5384935387 : ℕ)^8403*50000000000000^6355 ≤ 22055613014917^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384935387 10000000000 22055613014917 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1104176477/5000000000 : ℝ), (5218312389/10000000000 : ℝ), (5384935387/10000000000 : ℝ)] ![(13573258047939/100000000000000 : ℝ), (21157757953817/50000000000000 : ℝ), (22055613014917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1104176477/5000000000 : ℝ)|^8403 ≤ (13573258047939/100000000000000 : ℝ)^6355
        have hw : |(-1104176477/5000000000 : ℝ)|=(1104176477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218312389/10000000000 : ℝ)|^8403 ≤ (21157757953817/50000000000000 : ℝ)^6355
        have hw : |(5218312389/10000000000 : ℝ)|=(5218312389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384935387/10000000000 : ℝ)|^8403 ≤ (22055613014917/50000000000000 : ℝ)^6355
        have hw : |(5384935387/10000000000 : ℝ)|=(5384935387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_box_9 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (211591049/400000000 : ℝ)*x 0 + (-211319377/1000000000 : ℝ)*x 1 + (538493539/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211591049/400000000 : ℝ)^8403 ≤ (2692716189167/6250000000000 : ℝ)^6355 := by
    have hnat : (211591049 : ℕ)^8403*6250000000000^6355 ≤ 2692716189167^6355*400000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211591049 400000000 2692716189167 6250000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211319377/1000000000 : ℝ)^8403 ≤ (64026574491/500000000000 : ℝ)^6355 := by
    have hnat : (211319377 : ℕ)^8403*500000000000^6355 ≤ 64026574491^6355*1000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211319377 1000000000 64026574491 500000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538493539/1000000000 : ℝ)^8403 ≤ (44111226062329/100000000000000 : ℝ)^6355 := by
    have hnat : (538493539 : ℕ)^8403*100000000000000^6355 ≤ 44111226062329^6355*1000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538493539 1000000000 44111226062329 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211591049/400000000 : ℝ), (-211319377/1000000000 : ℝ), (538493539/1000000000 : ℝ)] ![(2692716189167/6250000000000 : ℝ), (64026574491/500000000000 : ℝ), (44111226062329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211591049/400000000 : ℝ)|^8403 ≤ (2692716189167/6250000000000 : ℝ)^6355
        have hw : |(211591049/400000000 : ℝ)|=(211591049/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211319377/1000000000 : ℝ)|^8403 ≤ (64026574491/500000000000 : ℝ)^6355
        have hw : |(-211319377/1000000000 : ℝ)|=(211319377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538493539/1000000000 : ℝ)|^8403 ≤ (44111226062329/100000000000000 : ℝ)^6355
        have hw : |(538493539/1000000000 : ℝ)|=(538493539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_box_10 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (661222027/1250000000 : ℝ)*x 0 + (5384935389/10000000000 : ℝ)*x 1 + (-1056596891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661222027/1250000000 : ℝ)^8403 ≤ (10770864732437/25000000000000 : ℝ)^6355 := by
    have hnat : (661222027 : ℕ)^8403*25000000000000^6355 ≤ 10770864732437^6355*1250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661222027 1250000000 10770864732437 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5384935389/10000000000 : ℝ)^8403 ≤ (44111226051497/100000000000000 : ℝ)^6355 := by
    have hnat : (5384935389 : ℕ)^8403*100000000000000^6355 ≤ 44111226051497^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384935389 10000000000 44111226051497 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056596891/5000000000 : ℝ)^8403 ≤ (12805314994351/100000000000000 : ℝ)^6355 := by
    have hnat : (1056596891 : ℕ)^8403*100000000000000^6355 ≤ 12805314994351^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056596891 5000000000 12805314994351 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661222027/1250000000 : ℝ), (5384935389/10000000000 : ℝ), (-1056596891/5000000000 : ℝ)] ![(10770864732437/25000000000000 : ℝ), (44111226051497/100000000000000 : ℝ), (12805314994351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661222027/1250000000 : ℝ)|^8403 ≤ (10770864732437/25000000000000 : ℝ)^6355
        have hw : |(661222027/1250000000 : ℝ)|=(661222027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5384935389/10000000000 : ℝ)|^8403 ≤ (44111226051497/100000000000000 : ℝ)^6355
        have hw : |(5384935389/10000000000 : ℝ)|=(5384935389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1056596891/5000000000 : ℝ)|^8403 ≤ (12805314994351/100000000000000 : ℝ)^6355
        have hw : |(-1056596891/5000000000 : ℝ)|=(1056596891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_box_11 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4483794811/10000000000 : ℝ)*x 0 + (4292798591/10000000000 : ℝ)*x 1 + (1073199639/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4483794811/10000000000 : ℝ)^8403 ≤ (1384978424049/4000000000000 : ℝ)^6355 := by
    have hnat : (4483794811 : ℕ)^8403*4000000000000^6355 ≤ 1384978424049^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483794811 10000000000 1384978424049 4000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4292798591/10000000000 : ℝ)^8403 ≤ (1021492808357/3125000000000 : ℝ)^6355 := by
    have hnat : (4292798591 : ℕ)^8403*3125000000000^6355 ≤ 1021492808357^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4292798591 10000000000 1021492808357 3125000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073199639/2500000000 : ℝ)^8403 ≤ (8171942378757/25000000000000 : ℝ)^6355 := by
    have hnat : (1073199639 : ℕ)^8403*25000000000000^6355 ≤ 8171942378757^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073199639 2500000000 8171942378757 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4483794811/10000000000 : ℝ), (4292798591/10000000000 : ℝ), (1073199639/2500000000 : ℝ)] ![(1384978424049/4000000000000 : ℝ), (1021492808357/3125000000000 : ℝ), (8171942378757/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4483794811/10000000000 : ℝ)|^8403 ≤ (1384978424049/4000000000000 : ℝ)^6355
        have hw : |(4483794811/10000000000 : ℝ)|=(4483794811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4292798591/10000000000 : ℝ)|^8403 ≤ (1021492808357/3125000000000 : ℝ)^6355
        have hw : |(4292798591/10000000000 : ℝ)|=(4292798591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1073199639/2500000000 : ℝ)|^8403 ≤ (8171942378757/25000000000000 : ℝ)^6355
        have hw : |(1073199639/2500000000 : ℝ)|=(1073199639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_box_12 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-257860277/1250000000 : ℝ)*x 0 + (2718862921/5000000000 : ℝ)*x 1 + (527387801/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257860277/1250000000 : ℝ)^8403 ≤ (3100936722623/25000000000000 : ℝ)^6355 := by
    have hnat : (257860277 : ℕ)^8403*25000000000000^6355 ≤ 3100936722623^6355*1250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257860277 1250000000 3100936722623 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718862921/5000000000 : ℝ)^8403 ≤ (5585490694659/12500000000000 : ℝ)^6355 := by
    have hnat : (2718862921 : ℕ)^8403*12500000000000^6355 ≤ 5585490694659^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718862921 5000000000 5585490694659 12500000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527387801/1000000000 : ℝ)^8403 ≤ (10728081884857/25000000000000 : ℝ)^6355 := by
    have hnat : (527387801 : ℕ)^8403*25000000000000^6355 ≤ 10728081884857^6355*1000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527387801 1000000000 10728081884857 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257860277/1250000000 : ℝ), (2718862921/5000000000 : ℝ), (527387801/1000000000 : ℝ)] ![(3100936722623/25000000000000 : ℝ), (5585490694659/12500000000000 : ℝ), (10728081884857/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257860277/1250000000 : ℝ)|^8403 ≤ (3100936722623/25000000000000 : ℝ)^6355
        have hw : |(-257860277/1250000000 : ℝ)|=(257860277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718862921/5000000000 : ℝ)|^8403 ≤ (5585490694659/12500000000000 : ℝ)^6355
        have hw : |(2718862921/5000000000 : ℝ)|=(2718862921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527387801/1000000000 : ℝ)|^8403 ≤ (10728081884857/25000000000000 : ℝ)^6355
        have hw : |(527387801/1000000000 : ℝ)|=(527387801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_box_13 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368120189/10000000000 : ℝ)*x 0 + (-1078562383/5000000000 : ℝ)*x 1 + (1054775621/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368120189/10000000000 : ℝ)^8403 ≤ (10982296101861/25000000000000 : ℝ)^6355 := by
    have hnat : (5368120189 : ℕ)^8403*25000000000000^6355 ≤ 10982296101861^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368120189 10000000000 10982296101861 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078562383/5000000000 : ℝ)^8403 ≤ (13158487014539/100000000000000 : ℝ)^6355 := by
    have hnat : (1078562383 : ℕ)^8403*100000000000000^6355 ≤ 13158487014539^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078562383 5000000000 13158487014539 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054775621/2000000000 : ℝ)^8403 ≤ (4291232856153/10000000000000 : ℝ)^6355 := by
    have hnat : (1054775621 : ℕ)^8403*10000000000000^6355 ≤ 4291232856153^6355*2000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054775621 2000000000 4291232856153 10000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368120189/10000000000 : ℝ), (-1078562383/5000000000 : ℝ), (1054775621/2000000000 : ℝ)] ![(10982296101861/25000000000000 : ℝ), (13158487014539/100000000000000 : ℝ), (4291232856153/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368120189/10000000000 : ℝ)|^8403 ≤ (10982296101861/25000000000000 : ℝ)^6355
        have hw : |(5368120189/10000000000 : ℝ)|=(5368120189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1078562383/5000000000 : ℝ)|^8403 ≤ (13158487014539/100000000000000 : ℝ)^6355
        have hw : |(-1078562383/5000000000 : ℝ)|=(1078562383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054775621/2000000000 : ℝ)|^8403 ≤ (4291232856153/10000000000000 : ℝ)^6355
        have hw : |(1054775621/2000000000 : ℝ)|=(1054775621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_box_14 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368120363/10000000000 : ℝ)*x 0 + (105477561/200000000 : ℝ)*x 1 + (-1078562303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368120363/10000000000 : ℝ)^8403 ≤ (21964593145111/50000000000000 : ℝ)^6355 := by
    have hnat : (5368120363 : ℕ)^8403*50000000000000^6355 ≤ 21964593145111^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368120363 10000000000 21964593145111 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105477561/200000000 : ℝ)^8403 ≤ (42912327969787/100000000000000 : ℝ)^6355 := by
    have hnat : (105477561 : ℕ)^8403*100000000000000^6355 ≤ 42912327969787^6355*200000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105477561 200000000 42912327969787 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078562303/5000000000 : ℝ)^8403 ≤ (2631697144801/20000000000000 : ℝ)^6355 := by
    have hnat : (1078562303 : ℕ)^8403*20000000000000^6355 ≤ 2631697144801^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078562303 5000000000 2631697144801 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368120363/10000000000 : ℝ), (105477561/200000000 : ℝ), (-1078562303/5000000000 : ℝ)] ![(21964593145111/50000000000000 : ℝ), (42912327969787/100000000000000 : ℝ), (2631697144801/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368120363/10000000000 : ℝ)|^8403 ≤ (21964593145111/50000000000000 : ℝ)^6355
        have hw : |(5368120363/10000000000 : ℝ)|=(5368120363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105477561/200000000 : ℝ)|^8403 ≤ (42912327969787/100000000000000 : ℝ)^6355
        have hw : |(105477561/200000000 : ℝ)|=(105477561/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1078562303/5000000000 : ℝ)|^8403 ≤ (2631697144801/20000000000000 : ℝ)^6355
        have hw : |(-1078562303/5000000000 : ℝ)|=(1078562303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_box_15 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2114609501/5000000000 : ℝ)*x 0 + (4420084341/10000000000 : ℝ)*x 1 + (884016783/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114609501/5000000000 : ℝ)^8403 ≤ (16024576692773/50000000000000 : ℝ)^6355 := by
    have hnat : (2114609501 : ℕ)^8403*50000000000000^6355 ≤ 16024576692773^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114609501 5000000000 16024576692773 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4420084341/10000000000 : ℝ)^8403 ≤ (16987712732703/50000000000000 : ℝ)^6355 := by
    have hnat : (4420084341 : ℕ)^8403*50000000000000^6355 ≤ 16987712732703^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4420084341 10000000000 16987712732703 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (884016783/2000000000 : ℝ)^8403 ≤ (33975421135657/100000000000000 : ℝ)^6355 := by
    have hnat : (884016783 : ℕ)^8403*100000000000000^6355 ≤ 33975421135657^6355*2000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884016783 2000000000 33975421135657 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114609501/5000000000 : ℝ), (4420084341/10000000000 : ℝ), (884016783/2000000000 : ℝ)] ![(16024576692773/50000000000000 : ℝ), (16987712732703/50000000000000 : ℝ), (33975421135657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114609501/5000000000 : ℝ)|^8403 ≤ (16024576692773/50000000000000 : ℝ)^6355
        have hw : |(2114609501/5000000000 : ℝ)|=(2114609501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4420084341/10000000000 : ℝ)|^8403 ≤ (16987712732703/50000000000000 : ℝ)^6355
        have hw : |(4420084341/10000000000 : ℝ)|=(4420084341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(884016783/2000000000 : ℝ)|^8403 ≤ (33975421135657/100000000000000 : ℝ)^6355
        have hw : |(884016783/2000000000 : ℝ)|=(884016783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1210_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (143/1250 : ℝ)*pair X i i ≤ pair X i h) :
    -(62241/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7419/12500 : ℝ) ∧ (40007/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20819/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (143/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (143/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (143/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (143/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (143/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (143/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (143/1250 : ℝ) ^ (4201/1024 : ℝ) ≤ (13713742327899327/100000000000000000000 : ℝ) := by
    have hpowers : (143/1250 : ℝ)^4201 ≤ (13713742327899327/100000000000000000000 : ℝ)^1024 := by
      have hnat : (143 : ℕ)^4201*100000000000000000000^1024 ≤ 13713742327899327^1024*1250^4201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        143 1250 13713742327899327 100000000000000000000 4201 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (143/1250 : ℝ)) (X := (13713742327899327/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14087/100000 : ℝ) ^ (4201/1024 : ℝ) ≤ (32210295335749603/100000000000000000000 : ℝ) := by
    have hpowers : (14087/100000 : ℝ)^4201 ≤ (32210295335749603/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14087 : ℕ)^4201*100000000000000000000^1024 ≤ 32210295335749603^1024*100000^4201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14087 100000 32210295335749603 100000000000000000000 4201 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14087/100000 : ℝ)) (X := (32210295335749603/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013713742327899327/50000000000000000000 : ℝ) ≤ (2000133695938983/2000000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (50013713742327899327/50000000000000000000 : ℝ)^1024 ≤ (2000133695938983/2000000000000000 : ℝ)^4201 := by
      have hnat : (50013713742327899327 : ℕ)^1024*2000000000000000^4201 ≤ 2000133695938983^4201*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013713742327899327 50000000000000000000 2000133695938983 2000000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000133695938983/2000000000000000 : ℝ)) (X := (50013713742327899327/50000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004592403766364893/10000000000000000000 : ℝ) ≤ (2500279802729491/2500000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (10004592403766364893/10000000000000000000 : ℝ)^1024 ≤ (2500279802729491/2500000000000000 : ℝ)^4201 := by
      have hnat : (10004592403766364893 : ℕ)^1024*2500000000000000^4201 ≤ 2500279802729491^4201*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004592403766364893 10000000000000000000 2500279802729491 2500000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500279802729491/2500000000000000 : ℝ)) (X := (10004592403766364893/10000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032210295335749603/50000000000000000000 : ℝ) ≤ (10001569942141013/10000000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (50032210295335749603/50000000000000000000 : ℝ)^1024 ≤ (10001569942141013/10000000000000000 : ℝ)^4201 := by
      have hnat : (50032210295335749603 : ℕ)^1024*10000000000000000^4201 ≤ 10001569942141013^4201*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032210295335749603 50000000000000000000 10001569942141013 10000000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001569942141013/10000000000000000 : ℝ)) (X := (50032210295335749603/50000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13713742327899327/100000000000000000000 : ℝ) ≤ ((5292291347073815777/5294000000000000000 : ℝ)+2*(450731223049/264700000000000 : ℝ)*(143/1250 : ℝ))^(4201/1024 : ℝ) := by
    rw [show (5292291347073815777/5294000000000000000 : ℝ)+2*(450731223049/264700000000000 : ℝ)*(143/1250 : ℝ)=(2000133695938983/2000000000000000 : ℝ) by norm_num, show 1+2*(13713742327899327/100000000000000000000 : ℝ)=(50013713742327899327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32210295335749603/100000000000000000000 : ℝ)+(13713742327899327/100000000000000000000 : ℝ) ≤ ((5292291347073815777/5294000000000000000 : ℝ)+(450731223049/264700000000000 : ℝ)*((14087/100000 : ℝ)+(143/1250 : ℝ)))^(4201/1024 : ℝ) := by
    rw [show (5292291347073815777/5294000000000000000 : ℝ)+(450731223049/264700000000000 : ℝ)*((14087/100000 : ℝ)+(143/1250 : ℝ))=(2500279802729491/2500000000000000 : ℝ) by norm_num, show 1+(32210295335749603/100000000000000000000 : ℝ)+(13713742327899327/100000000000000000000 : ℝ)=(10004592403766364893/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32210295335749603/100000000000000000000 : ℝ) ≤ ((5292291347073815777/5294000000000000000 : ℝ)+2*(450731223049/264700000000000 : ℝ)*(14087/100000 : ℝ))^(4201/1024 : ℝ) := by
    rw [show (5292291347073815777/5294000000000000000 : ℝ)+2*(450731223049/264700000000000 : ℝ)*(14087/100000 : ℝ)=(10001569942141013/10000000000000000 : ℝ) by norm_num, show 1+2*(32210295335749603/100000000000000000000 : ℝ)=(50032210295335749603/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5292291347073815777/5294000000000000000 : ℝ)*(X 1 0+X 2 0)+(450731223049/264700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (143/1250 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (5292291347073815777/5294000000000000000 : ℝ)) (alpha := (450731223049/264700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5292291347073815777/5294000000000000000 : ℝ)*(X 0 1+X 2 1)+(450731223049/264700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (143/1250 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (5292291347073815777/5294000000000000000 : ℝ)) (alpha := (450731223049/264700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5292291347073815777/5294000000000000000 : ℝ)*(X 0 2+X 1 2)+(450731223049/264700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (143/1250 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (5292291347073815777/5294000000000000000 : ℝ)) (alpha := (450731223049/264700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-402017153/2000000000 : ℝ)*X 0 0+(1343830707/2500000000 : ℝ)*X 0 1+(1075064513/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2648280177/5000000000 : ℝ)*X 1 0+(-13231649/62500000 : ℝ)*X 1 1+(2687661129/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296561053/10000000000 : ℝ)*X 2 0+(537532227/1000000000 : ℝ)*X 2 1+(-529265721/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4462028599/10000000000 : ℝ)*X 0 0+(4303821567/10000000000 : ℝ)*X 0 1+(4303822889/10000000000 : ℝ)*X 0 2+(4462028599/10000000000 : ℝ)*X 1 0+(4303821567/10000000000 : ℝ)*X 1 1+(4303822889/10000000000 : ℝ)*X 1 2+(4462028599/10000000000 : ℝ)*X 2 0+(4303821567/10000000000 : ℝ)*X 2 1+(4303822889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-282608853/1250000000 : ℝ)*X 0 0+(2640972847/5000000000 : ℝ)*X 0 1+(5281945733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((268121559/500000000 : ℝ)*X 1 0+(-430798149/2000000000 : ℝ)*X 1 1+(1320486423/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((67030389/125000000 : ℝ)*X 2 0+(528194573/1000000000 : ℝ)*X 2 1+(-86159631/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4247947121/10000000000 : ℝ)*X 0 0+(2205421323/5000000000 : ℝ)*X 0 1+(2205421313/5000000000 : ℝ)*X 0 2+(4247947121/10000000000 : ℝ)*X 1 0+(2205421323/5000000000 : ℝ)*X 1 1+(2205421313/5000000000 : ℝ)*X 1 2+(4247947121/10000000000 : ℝ)*X 2 0+(2205421323/5000000000 : ℝ)*X 2 1+(2205421313/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1104176477/5000000000 : ℝ)*X 0 0+(5218312389/10000000000 : ℝ)*X 0 1+(5384935387/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((211591049/400000000 : ℝ)*X 1 0+(-211319377/1000000000 : ℝ)*X 1 1+(538493539/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((661222027/1250000000 : ℝ)*X 2 0+(5384935389/10000000000 : ℝ)*X 2 1+(-1056596891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4483794811/10000000000 : ℝ)*X 0 0+(4292798591/10000000000 : ℝ)*X 0 1+(1073199639/2500000000 : ℝ)*X 0 2+(4483794811/10000000000 : ℝ)*X 1 0+(4292798591/10000000000 : ℝ)*X 1 1+(1073199639/2500000000 : ℝ)*X 1 2+(4483794811/10000000000 : ℝ)*X 2 0+(4292798591/10000000000 : ℝ)*X 2 1+(1073199639/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-257860277/1250000000 : ℝ)*X 0 0+(2718862921/5000000000 : ℝ)*X 0 1+(527387801/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368120189/10000000000 : ℝ)*X 1 0+(-1078562383/5000000000 : ℝ)*X 1 1+(1054775621/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368120363/10000000000 : ℝ)*X 2 0+(105477561/200000000 : ℝ)*X 2 1+(-1078562303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2114609501/5000000000 : ℝ)*X 0 0+(4420084341/10000000000 : ℝ)*X 0 1+(884016783/2000000000 : ℝ)*X 0 2+(2114609501/5000000000 : ℝ)*X 1 0+(4420084341/10000000000 : ℝ)*X 1 1+(884016783/2000000000 : ℝ)*X 1 2+(2114609501/5000000000 : ℝ)*X 2 0+(4420084341/10000000000 : ℝ)*X 2 1+(884016783/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62241/100000 : ℝ) ≤ (-41186255804282263309689984167331/66175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34280503/100000000000000 : ℝ)*(upper1) + (619791/1562500000000 : ℝ)*(lower4) + (17206101/100000000000000 : ℝ)*(upper5) + (994183355074999/25000000000000 : ℝ)*(major0) + (994183355074999/25000000000000 : ℝ)*(major1) + (994183355074999/25000000000000 : ℝ)*(major2) + (89663567/4000000000000 : ℝ)*(sp3) + (2668580039018511/50000000000000 : ℝ)*(sp4) + (2668572355093183/50000000000000 : ℝ)*(sp5) + (2668579073054399/50000000000000 : ℝ)*(sp6) + (2637050624182239/100000000000000 : ℝ)*(sp7) + (13703489/50000000000000 : ℝ)*(sp12) + (7697628817/50000000000000 : ℝ)*(sp13) + (1959335201/100000000000000 : ℝ)*(sp14) + (1318526432885707/50000000000000 : ℝ)*(f.failure) + (1334290026361/25000000000 : ℝ)*(f.sum) + (13320185796831/3308750000000000000000000000 : ℝ)*base65 + (595275356559570777/132350000000000000000000000000000 : ℝ)*base68 + (279423578960229223/132350000000000000000000000000000 : ℝ)*base69 + (592661984974020777/132350000000000000000000000000000 : ℝ)*base72 + (105181730346129/13235000000000000000000000000 : ℝ)*base73 + (645522481130629223/132350000000000000000000000000000 : ℝ)*base75 + (1009660705673970777/132350000000000000000000000000000 : ℝ)*base78 + (67273216877670777/132350000000000000000000000000000 : ℝ)*base80 + (36081839974549/13235000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (7618271/1250000000000000000000 : ℝ)*base90 + (7618271/1250000000000000000000 : ℝ)*base92 + (7618271/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (7419/12500 : ℝ) ≤ (1571104647689283488119222221/2647000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117785451/100000000000000 : ℝ)*(upper0) + (494656023/100000000000000 : ℝ)*(lower1) + (637068031/100000000000000 : ℝ)*(upper4) + (2695281/2500000000000 : ℝ)*(upper5) + (808395350402929/20000000000000 : ℝ)*(major0) + (808395350402929/20000000000000 : ℝ)*(major1) + (808395350402929/20000000000000 : ℝ)*(major2) + (2691925868375833/50000000000000 : ℝ)*(sp0) + (1076633047608449/20000000000000 : ℝ)*(sp1) + (1076709920611823/20000000000000 : ℝ)*(sp2) + (67007882758591/2500000000000 : ℝ)*(sp3) + (868262417/50000000000000 : ℝ)*(sp7) + (34324935471/5000000000000 : ℝ)*(sp9) + (302133692551/100000000000000 : ℝ)*(sp10) + (1340158523434237/50000000000000 : ℝ)*(f.failure) + (2691925868375833/50000000000000 : ℝ)*(f.sum) + (5592584919273/2647000000000000000000000000 : ℝ)*base65 + (2688082898743329167/105880000000000000000000000000000 : ℝ)*base68 + (517920382473710833/105880000000000000000000000000000 : ℝ)*base69 + (394118692154110833/105880000000000000000000000000000 : ℝ)*base71 + (155413550304747/2647000000000000000000000000 : ℝ)*base74 + (1266913414520110833/105880000000000000000000000000000 : ℝ)*base75 + (257903146726169167/105880000000000000000000000000000 : ℝ)*base78 + (707570704856409167/105880000000000000000000000000000 : ℝ)*base80 + (9990269113727/2647000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (9072361/1250000000000000000000 : ℝ)*base90 + (9072361/1250000000000000000000 : ℝ)*base92 + (9072361/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40007/50000 : ℝ) ≤ (211803008617741589959816622275311/264700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5170059/100000000000000 : ℝ)*(upper1) + (183837/5000000000000 : ℝ)*(upper2) + (7228761/100000000000000 : ℝ)*(upper3) + (10003/160000000000 : ℝ)*(lower5) + (4509190134345527/100000000000000 : ℝ)*(major0) + (4509190134345527/100000000000000 : ℝ)*(major1) + (4509190134345527/100000000000000 : ℝ)*(major2) + (53726421/20000000000000 : ℝ)*(sp0) + (508390969/20000000000000 : ℝ)*(sp2) + (1287022711/100000000000000 : ℝ)*(sp3) + (6001572167918773/100000000000000 : ℝ)*(sp8) + (6001572436550877/100000000000000 : ℝ)*(sp9) + (93774529603063/1562500000000 : ℝ)*(sp10) + (119605378497217/4000000000000 : ℝ)*(sp11) + (186883484340821/6250000000000 : ℝ)*(f.failure) + (6001572436550877/100000000000000 : ℝ)*(f.sum) + (5166339051783/827187500000000000000000000 : ℝ)*base65 + (4908740508902160521/529400000000000000000000000000000 : ℝ)*base68 + (1862126574938560521/529400000000000000000000000000000 : ℝ)*base70 + (2729213912138160521/529400000000000000000000000000000 : ℝ)*base72 + (5917217044347/13235000000000000000000000000 : ℝ)*base74 + (4262197238026160521/529400000000000000000000000000000 : ℝ)*base76 + (1329335982874960521/529400000000000000000000000000000 : ℝ)*base78 + (6182954936455560521/529400000000000000000000000000000 : ℝ)*base80 + (40414806884349/6617500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (191587/156250000000000000000 : ℝ)*base89 + (191587/156250000000000000000 : ℝ)*base91 + (191587/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-20819/25000 : ℝ) ≤ (-220423924056895861820364952742019/264700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62996247/100000000000000 : ℝ)*(lower0) + (17663897/12500000000000 : ℝ)*(lower2) + (106797017/100000000000000 : ℝ)*(upper3) + (119726531/100000000000000 : ℝ)*(upper5) + (4544505225181151/100000000000000 : ℝ)*(major0) + (4544505225181151/100000000000000 : ℝ)*(major1) + (4544505225181151/100000000000000 : ℝ)*(major2) + (96650873/100000000000000 : ℝ)*(sp0) + (6172471801/10000000000000 : ℝ)*(sp5) + (19180626569/20000000000000 : ℝ)*(sp7) + (3051607076180403/50000000000000 : ℝ)*(sp12) + (610315252429367/10000000000000 : ℝ)*(sp13) + (6103214249011679/100000000000000 : ℝ)*(sp14) + (1506729000894357/50000000000000 : ℝ)*(sp15) + (3013553904921559/100000000000000 : ℝ)*(f.failure) + (6103214249011679/100000000000000 : ℝ)*(f.sum) + (27522271356379/13235000000000000000000000000 : ℝ)*base65 + (3901231162881200673/529400000000000000000000000000000 : ℝ)*base68 + (6530331801515799327/529400000000000000000000000000000 : ℝ)*base69 + (4951124147113400673/529400000000000000000000000000000 : ℝ)*base72 + (278310923919009/13235000000000000000000000000 : ℝ)*base73 + (2323503600155200673/529400000000000000000000000000000 : ℝ)*base76 + (215150666404799327/529400000000000000000000000000000 : ℝ)*base77 + (16603955702428800673/529400000000000000000000000000000 : ℝ)*base80 + (22281418438011/13235000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (8607227/2500000000000000000000 : ℝ)*base90 + (8607227/2500000000000000000000 : ℝ)*base92 + (8607227/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1210_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (143/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62241/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7419/12500 : ℝ) else (40007/50000 : ℝ) ≤ X j i ∧ X j i ≤ (20819/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1210_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1210_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (143/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62241/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7419/12500 : ℝ) else (40007/50000 : ℝ) ≤ X j i ∧ X j i ≤ (20819/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1210_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (143/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62241/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7419/12500 : ℝ) else (40007/50000 : ℝ) ≤ X j i ∧ X j i ≤ (20819/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1210_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

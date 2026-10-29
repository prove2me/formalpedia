-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1747_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:18:29.110244+00:00
-- url     : https://prove2.me/submissions/24674410-f4c6-4e53-b02d-3efd9ca3c0db

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
theorem support_rectangle_w1747_s3_0 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1239092581/10000000000 : ℝ)*x 0 + (1375272927/2500000000 : ℝ)*x 1 + (1270055343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1239092581/10000000000 : ℝ)^5727 ≤ (62911809377/800000000000 : ℝ)^4703 := by
    have hnat : (1239092581 : ℕ)^5727*800000000000^4703 ≤ 62911809377^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239092581 10000000000 62911809377 800000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1375272927/2500000000 : ℝ)^5727 ≤ (48298756360943/100000000000000 : ℝ)^4703 := by
    have hnat : (1375272927 : ℕ)^5727*100000000000000^4703 ≤ 48298756360943^4703*2500000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375272927 2500000000 48298756360943 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1270055343/2500000000 : ℝ)^5727 ≤ (10959316863277/25000000000000 : ℝ)^4703 := by
    have hnat : (1270055343 : ℕ)^5727*25000000000000^4703 ≤ 10959316863277^4703*2500000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270055343 2500000000 10959316863277 25000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1239092581/10000000000 : ℝ), (1375272927/2500000000 : ℝ), (1270055343/2500000000 : ℝ)] ![(62911809377/800000000000 : ℝ), (48298756360943/100000000000000 : ℝ), (10959316863277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1239092581/10000000000 : ℝ)|^5727 ≤ (62911809377/800000000000 : ℝ)^4703
        have hw : |(-1239092581/10000000000 : ℝ)|=(1239092581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1375272927/2500000000 : ℝ)|^5727 ≤ (48298756360943/100000000000000 : ℝ)^4703
        have hw : |(1375272927/2500000000 : ℝ)|=(1375272927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1270055343/2500000000 : ℝ)|^5727 ≤ (10959316863277/25000000000000 : ℝ)^4703
        have hw : |(1270055343/2500000000 : ℝ)|=(1270055343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s3_1 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2669192659/5000000000 : ℝ)*x 0 + (-729685467/5000000000 : ℝ)*x 1 + (635027657/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2669192659/5000000000 : ℝ)^5727 ≤ (46564823632643/100000000000000 : ℝ)^4703 := by
    have hnat : (2669192659 : ℕ)^5727*100000000000000^4703 ≤ 46564823632643^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2669192659 5000000000 46564823632643 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (729685467/5000000000 : ℝ)^5727 ≤ (4798955059559/50000000000000 : ℝ)^4703 := by
    have hnat : (729685467 : ℕ)^5727*50000000000000^4703 ≤ 4798955059559^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729685467 5000000000 4798955059559 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (635027657/1250000000 : ℝ)^5727 ≤ (43837266234199/100000000000000 : ℝ)^4703 := by
    have hnat : (635027657 : ℕ)^5727*100000000000000^4703 ≤ 43837266234199^4703*1250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635027657 1250000000 43837266234199 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2669192659/5000000000 : ℝ), (-729685467/5000000000 : ℝ), (635027657/1250000000 : ℝ)] ![(46564823632643/100000000000000 : ℝ), (4798955059559/50000000000000 : ℝ), (43837266234199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2669192659/5000000000 : ℝ)|^5727 ≤ (46564823632643/100000000000000 : ℝ)^4703
        have hw : |(2669192659/5000000000 : ℝ)|=(2669192659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-729685467/5000000000 : ℝ)|^5727 ≤ (4798955059559/50000000000000 : ℝ)^4703
        have hw : |(-729685467/5000000000 : ℝ)|=(729685467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(635027657/1250000000 : ℝ)|^5727 ≤ (43837266234199/100000000000000 : ℝ)^4703
        have hw : |(635027657/1250000000 : ℝ)|=(635027657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s3_2 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (667298129/1250000000 : ℝ)*x 0 + (254011087/500000000 : ℝ)*x 1 + (-1459370679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667298129/1250000000 : ℝ)^5727 ≤ (46564820594793/100000000000000 : ℝ)^4703 := by
    have hnat : (667298129 : ℕ)^5727*100000000000000^4703 ≤ 46564820594793^4703*1250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667298129 1250000000 46564820594793 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254011087/500000000 : ℝ)^5727 ≤ (43837271319989/100000000000000 : ℝ)^4703 := by
    have hnat : (254011087 : ℕ)^5727*100000000000000^4703 ≤ 43837271319989^4703*500000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254011087 500000000 43837271319989 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1459370679/10000000000 : ℝ)^5727 ≤ (4798954038447/50000000000000 : ℝ)^4703 := by
    have hnat : (1459370679 : ℕ)^5727*50000000000000^4703 ≤ 4798954038447^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459370679 10000000000 4798954038447 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(667298129/1250000000 : ℝ), (254011087/500000000 : ℝ), (-1459370679/10000000000 : ℝ)] ![(46564820594793/100000000000000 : ℝ), (43837271319989/100000000000000 : ℝ), (4798954038447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(667298129/1250000000 : ℝ)|^5727 ≤ (46564820594793/100000000000000 : ℝ)^4703
        have hw : |(667298129/1250000000 : ℝ)|=(667298129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(254011087/500000000 : ℝ)|^5727 ≤ (43837271319989/100000000000000 : ℝ)^4703
        have hw : |(254011087/500000000 : ℝ)|=(254011087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1459370679/10000000000 : ℝ)|^5727 ≤ (4798954038447/50000000000000 : ℝ)^4703
        have hw : |(-1459370679/10000000000 : ℝ)|=(1459370679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s3_3 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2013589647/5000000000 : ℝ)*x 0 + (422022717/1250000000 : ℝ)*x 1 + (4742063519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2013589647/5000000000 : ℝ)^5727 ≤ (33036687672801/100000000000000 : ℝ)^4703 := by
    have hnat : (2013589647 : ℕ)^5727*100000000000000^4703 ≤ 33036687672801^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013589647 5000000000 33036687672801 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422022717/1250000000 : ℝ)^5727 ≤ (5330628040771/20000000000000 : ℝ)^4703 := by
    have hnat : (422022717 : ℕ)^5727*20000000000000^4703 ≤ 5330628040771^4703*1250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422022717 1250000000 5330628040771 20000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4742063519/10000000000 : ℝ)^5727 ≤ (40310172114231/100000000000000 : ℝ)^4703 := by
    have hnat : (4742063519 : ℕ)^5727*100000000000000^4703 ≤ 40310172114231^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4742063519 10000000000 40310172114231 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2013589647/5000000000 : ℝ), (422022717/1250000000 : ℝ), (4742063519/10000000000 : ℝ)] ![(33036687672801/100000000000000 : ℝ), (5330628040771/20000000000000 : ℝ), (40310172114231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2013589647/5000000000 : ℝ)|^5727 ≤ (33036687672801/100000000000000 : ℝ)^4703
        have hw : |(2013589647/5000000000 : ℝ)|=(2013589647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422022717/1250000000 : ℝ)|^5727 ≤ (5330628040771/20000000000000 : ℝ)^4703
        have hw : |(422022717/1250000000 : ℝ)|=(422022717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4742063519/10000000000 : ℝ)|^5727 ≤ (40310172114231/100000000000000 : ℝ)^4703
        have hw : |(4742063519/10000000000 : ℝ)|=(4742063519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s3_4 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1239449669/10000000000 : ℝ)*x 0 + (5087033247/10000000000 : ℝ)*x 1 + (5494136799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1239449669/10000000000 : ℝ)^5727 ≤ (7866735984239/100000000000000 : ℝ)^4703 := by
    have hnat : (1239449669 : ℕ)^5727*100000000000000^4703 ≤ 7866735984239^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239449669 10000000000 7866735984239 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5087033247/10000000000 : ℝ)^5727 ≤ (21954427961627/50000000000000 : ℝ)^4703 := by
    have hnat : (5087033247 : ℕ)^5727*50000000000000^4703 ≤ 21954427961627^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5087033247 10000000000 21954427961627 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5494136799/10000000000 : ℝ)^5727 ≤ (48224408081881/100000000000000 : ℝ)^4703 := by
    have hnat : (5494136799 : ℕ)^5727*100000000000000^4703 ≤ 48224408081881^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494136799 10000000000 48224408081881 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1239449669/10000000000 : ℝ), (5087033247/10000000000 : ℝ), (5494136799/10000000000 : ℝ)] ![(7866735984239/100000000000000 : ℝ), (21954427961627/50000000000000 : ℝ), (48224408081881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1239449669/10000000000 : ℝ)|^5727 ≤ (7866735984239/100000000000000 : ℝ)^4703
        have hw : |(-1239449669/10000000000 : ℝ)|=(1239449669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5087033247/10000000000 : ℝ)|^5727 ≤ (21954427961627/50000000000000 : ℝ)^4703
        have hw : |(5087033247/10000000000 : ℝ)|=(5087033247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5494136799/10000000000 : ℝ)|^5727 ≤ (48224408081881/100000000000000 : ℝ)^4703
        have hw : |(5494136799/10000000000 : ℝ)|=(5494136799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s3_5 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045345877/2000000000 : ℝ)*x 0 + (-130681931/1250000000 : ℝ)*x 1 + (1373534237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045345877/2000000000 : ℝ)^5727 ≤ (22690773112337/50000000000000 : ℝ)^4703 := by
    have hnat : (1045345877 : ℕ)^5727*50000000000000^4703 ≤ 22690773112337^4703*2000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045345877 2000000000 22690773112337 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130681931/1250000000 : ℝ)^5727 ≤ (3197022043511/50000000000000 : ℝ)^4703 := by
    have hnat : (130681931 : ℕ)^5727*50000000000000^4703 ≤ 3197022043511^4703*1250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130681931 1250000000 3197022043511 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1373534237/2500000000 : ℝ)^5727 ≤ (24112204837239/50000000000000 : ℝ)^4703 := by
    have hnat : (1373534237 : ℕ)^5727*50000000000000^4703 ≤ 24112204837239^4703*2500000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373534237 2500000000 24112204837239 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045345877/2000000000 : ℝ), (-130681931/1250000000 : ℝ), (1373534237/2500000000 : ℝ)] ![(22690773112337/50000000000000 : ℝ), (3197022043511/50000000000000 : ℝ), (24112204837239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045345877/2000000000 : ℝ)|^5727 ≤ (22690773112337/50000000000000 : ℝ)^4703
        have hw : |(1045345877/2000000000 : ℝ)|=(1045345877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130681931/1250000000 : ℝ)|^5727 ≤ (3197022043511/50000000000000 : ℝ)^4703
        have hw : |(-130681931/1250000000 : ℝ)|=(130681931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1373534237/2500000000 : ℝ)|^5727 ≤ (24112204837239/50000000000000 : ℝ)^4703
        have hw : |(1373534237/2500000000 : ℝ)|=(1373534237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s3_6 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2613364733/5000000000 : ℝ)*x 0 + (5494136793/10000000000 : ℝ)*x 1 + (-261363889/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613364733/5000000000 : ℝ)^5727 ≤ (45381547081093/100000000000000 : ℝ)^4703 := by
    have hnat : (2613364733 : ℕ)^5727*100000000000000^4703 ≤ 45381547081093^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613364733 5000000000 45381547081093 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5494136793/10000000000 : ℝ)^5727 ≤ (48224408017749/100000000000000 : ℝ)^4703 := by
    have hnat : (5494136793 : ℕ)^5727*100000000000000^4703 ≤ 48224408017749^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494136793 10000000000 48224408017749 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261363889/2500000000 : ℝ)^5727 ≤ (3197022445687/50000000000000 : ℝ)^4703 := by
    have hnat : (261363889 : ℕ)^5727*50000000000000^4703 ≤ 3197022445687^4703*2500000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261363889 2500000000 3197022445687 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613364733/5000000000 : ℝ), (5494136793/10000000000 : ℝ), (-261363889/2500000000 : ℝ)] ![(45381547081093/100000000000000 : ℝ), (48224408017749/100000000000000 : ℝ), (3197022445687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613364733/5000000000 : ℝ)|^5727 ≤ (45381547081093/100000000000000 : ℝ)^4703
        have hw : |(2613364733/5000000000 : ℝ)|=(2613364733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5494136793/10000000000 : ℝ)|^5727 ≤ (48224408017749/100000000000000 : ℝ)^4703
        have hw : |(5494136793/10000000000 : ℝ)|=(5494136793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-261363889/2500000000 : ℝ)|^5727 ≤ (3197022445687/50000000000000 : ℝ)^4703
        have hw : |(-261363889/2500000000 : ℝ)|=(261363889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_s3_7 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1007084299/2500000000 : ℝ)*x 0 + (4719957333/10000000000 : ℝ)*x 1 + (3398753359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1007084299/2500000000 : ℝ)^5727 ≤ (6609651000603/20000000000000 : ℝ)^4703 := by
    have hnat : (1007084299 : ℕ)^5727*20000000000000^4703 ≤ 6609651000603^4703*2500000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007084299 2500000000 6609651000603 20000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4719957333/10000000000 : ℝ)^5727 ≤ (20040729102251/50000000000000 : ℝ)^4703 := by
    have hnat : (4719957333 : ℕ)^5727*50000000000000^4703 ≤ 20040729102251^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4719957333 10000000000 20040729102251 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3398753359/10000000000 : ℝ)^5727 ≤ (2687028678197/10000000000000 : ℝ)^4703 := by
    have hnat : (3398753359 : ℕ)^5727*10000000000000^4703 ≤ 2687028678197^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3398753359 10000000000 2687028678197 10000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1007084299/2500000000 : ℝ), (4719957333/10000000000 : ℝ), (3398753359/10000000000 : ℝ)] ![(6609651000603/20000000000000 : ℝ), (20040729102251/50000000000000 : ℝ), (2687028678197/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1007084299/2500000000 : ℝ)|^5727 ≤ (6609651000603/20000000000000 : ℝ)^4703
        have hw : |(1007084299/2500000000 : ℝ)|=(1007084299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4719957333/10000000000 : ℝ)|^5727 ≤ (20040729102251/50000000000000 : ℝ)^4703
        have hw : |(4719957333/10000000000 : ℝ)|=(4719957333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3398753359/10000000000 : ℝ)|^5727 ≤ (2687028678197/10000000000000 : ℝ)^4703
        have hw : |(3398753359/10000000000 : ℝ)|=(3398753359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1747_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26533597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3607/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/100 : ℝ)*pair X i i ≤ pair X i h) :
    (9001/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9017/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3607/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9/100 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3607/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9/100 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3607/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9/100 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3607/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9/100 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3607/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9/100 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3607/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9/100 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9/100 : ℝ) ^ (5711/1024 : ℝ) ≤ (147114420547219/100000000000000000000 : ℝ) := by
    have hpowers : (9/100 : ℝ)^5711 ≤ (147114420547219/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9 : ℕ)^5711*100000000000000000000^1024 ≤ 147114420547219^1024*100^5711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9 100 147114420547219 100000000000000000000 5711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9/100 : ℝ)) (X := (147114420547219/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3607/20000 : ℝ) ^ (5711/1024 : ℝ) ≤ (7099852554301429/100000000000000000000 : ℝ) := by
    have hpowers : (3607/20000 : ℝ)^5711 ≤ (7099852554301429/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3607 : ℕ)^5711*100000000000000000000^1024 ≤ 7099852554301429^1024*20000^5711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3607 20000 7099852554301429 100000000000000000000 5711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3607/20000 : ℝ)) (X := (7099852554301429/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000147114420547219/50000000000000000000 : ℝ) ≤ (5000002637803971/5000000000000000 : ℝ) ^ (5711/1024 : ℝ) := by
    have hpowers : (50000147114420547219/50000000000000000000 : ℝ)^1024 ≤ (5000002637803971/5000000000000000 : ℝ)^5711 := by
      have hnat : (50000147114420547219 : ℕ)^1024*5000000000000000^5711 ≤ 5000002637803971^5711*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000147114420547219 50000000000000000000 5000002637803971 5000000000000000 1024 5711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000002637803971/5000000000000000 : ℝ)) (X := (50000147114420547219/50000000000000000000 : ℝ)) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12500905870871856081/12500000000000000000 : ℝ) ≤ (5000064968249963/5000000000000000 : ℝ) ^ (5711/1024 : ℝ) := by
    have hpowers : (12500905870871856081/12500000000000000000 : ℝ)^1024 ≤ (5000064968249963/5000000000000000 : ℝ)^5711 := by
      have hnat : (12500905870871856081 : ℕ)^1024*5000000000000000^5711 ≤ 5000064968249963^5711*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500905870871856081 12500000000000000000 5000064968249963 5000000000000000 1024 5711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000064968249963/5000000000000000 : ℝ)) (X := (12500905870871856081/12500000000000000000 : ℝ)) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50007099852554301429/50000000000000000000 : ℝ) ≤ (1000025459739191/1000000000000000 : ℝ) ^ (5711/1024 : ℝ) := by
    have hpowers : (50007099852554301429/50000000000000000000 : ℝ)^1024 ≤ (1000025459739191/1000000000000000 : ℝ)^5711 := by
      have hnat : (50007099852554301429 : ℕ)^1024*1000000000000000^5711 ≤ 1000025459739191^5711*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007099852554301429 50000000000000000000 1000025459739191 1000000000000000 1024 5711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000025459739191/1000000000000000 : ℝ)) (X := (50007099852554301429/50000000000000000000 : ℝ)) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(147114420547219/100000000000000000000 : ℝ) ≤ ((9034780376906204397/9035000000000000000 : ℝ)+2*(7791305749/56468750000000 : ℝ)*(9/100 : ℝ))^(5711/1024 : ℝ) := by
    rw [show (9034780376906204397/9035000000000000000 : ℝ)+2*(7791305749/56468750000000 : ℝ)*(9/100 : ℝ)=(5000002637803971/5000000000000000 : ℝ) by norm_num, show 1+2*(147114420547219/100000000000000000000 : ℝ)=(50000147114420547219/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7099852554301429/100000000000000000000 : ℝ)+(147114420547219/100000000000000000000 : ℝ) ≤ ((9034780376906204397/9035000000000000000 : ℝ)+(7791305749/56468750000000 : ℝ)*((3607/20000 : ℝ)+(9/100 : ℝ)))^(5711/1024 : ℝ) := by
    rw [show (9034780376906204397/9035000000000000000 : ℝ)+(7791305749/56468750000000 : ℝ)*((3607/20000 : ℝ)+(9/100 : ℝ))=(5000064968249963/5000000000000000 : ℝ) by norm_num, show 1+(7099852554301429/100000000000000000000 : ℝ)+(147114420547219/100000000000000000000 : ℝ)=(12500905870871856081/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7099852554301429/100000000000000000000 : ℝ) ≤ ((9034780376906204397/9035000000000000000 : ℝ)+2*(7791305749/56468750000000 : ℝ)*(3607/20000 : ℝ))^(5711/1024 : ℝ) := by
    rw [show (9034780376906204397/9035000000000000000 : ℝ)+2*(7791305749/56468750000000 : ℝ)*(3607/20000 : ℝ)=(1000025459739191/1000000000000000 : ℝ) by norm_num, show 1+2*(7099852554301429/100000000000000000000 : ℝ)=(50007099852554301429/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9034780376906204397/9035000000000000000 : ℝ)*(X 1 0+X 2 0)+(7791305749/56468750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5711/1024 : ℝ)) (lo := (9/100 : ℝ)) (hi := (3607/20000 : ℝ)) (c := (9034780376906204397/9035000000000000000 : ℝ)) (alpha := (7791305749/56468750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9034780376906204397/9035000000000000000 : ℝ)*(X 0 1+X 2 1)+(7791305749/56468750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5711/1024 : ℝ)) (lo := (9/100 : ℝ)) (hi := (3607/20000 : ℝ)) (c := (9034780376906204397/9035000000000000000 : ℝ)) (alpha := (7791305749/56468750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9034780376906204397/9035000000000000000 : ℝ)*(X 0 2+X 1 2)+(7791305749/56468750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5711/1024 : ℝ)) (lo := (9/100 : ℝ)) (hi := (3607/20000 : ℝ)) (c := (9034780376906204397/9035000000000000000 : ℝ)) (alpha := (7791305749/56468750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1239092581/10000000000 : ℝ)*X 0 0+(1375272927/2500000000 : ℝ)*X 0 1+(1270055343/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2669192659/5000000000 : ℝ)*X 1 0+(-729685467/5000000000 : ℝ)*X 1 1+(635027657/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((667298129/1250000000 : ℝ)*X 2 0+(254011087/500000000 : ℝ)*X 2 1+(-1459370679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2013589647/5000000000 : ℝ)*X 0 0+(422022717/1250000000 : ℝ)*X 0 1+(4742063519/10000000000 : ℝ)*X 0 2+(2013589647/5000000000 : ℝ)*X 1 0+(422022717/1250000000 : ℝ)*X 1 1+(4742063519/10000000000 : ℝ)*X 1 2+(2013589647/5000000000 : ℝ)*X 2 0+(422022717/1250000000 : ℝ)*X 2 1+(4742063519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1239449669/10000000000 : ℝ)*X 0 0+(5087033247/10000000000 : ℝ)*X 0 1+(5494136799/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1045345877/2000000000 : ℝ)*X 1 0+(-130681931/1250000000 : ℝ)*X 1 1+(1373534237/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2613364733/5000000000 : ℝ)*X 2 0+(5494136793/10000000000 : ℝ)*X 2 1+(-261363889/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1007084299/2500000000 : ℝ)*X 0 0+(4719957333/10000000000 : ℝ)*X 0 1+(3398753359/10000000000 : ℝ)*X 0 2+(1007084299/2500000000 : ℝ)*X 1 0+(4719957333/10000000000 : ℝ)*X 1 1+(3398753359/10000000000 : ℝ)*X 1 2+(1007084299/2500000000 : ℝ)*X 2 0+(4719957333/10000000000 : ℝ)*X 2 1+(3398753359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16901949376846907612949321/2171875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5482533/400000000000 : ℝ)*(base19) + (131002023/12500000000000 : ℝ)*(base23) + (26067617/25000000000000 : ℝ)*(lower2) + (224342853/100000000000000 : ℝ)*(upper3) + (39786397/20000000000000 : ℝ)*(upper5) + (97130695385451/6250000000000 : ℝ)*(major0) + (97130695385451/6250000000000 : ℝ)*(major1) + (97130695385451/6250000000000 : ℝ)*(major2) + (1188019071455109/50000000000000 : ℝ)*(sp0) + (237604697765207/10000000000000 : ℝ)*(sp1) + (148502956266821/6250000000000 : ℝ)*(sp2) + (366065259825321/50000000000000 : ℝ)*(sp3) + (5102687551/50000000000000 : ℝ)*(sp4) + (3124992043/100000000000000 : ℝ)*(sp7) + (183033411160671/25000000000000 : ℝ)*(f.failure) + (59401208707133/2500000000000 : ℝ)*(f.sum) + (2419140940889/434375000000000000000000000 : ℝ)*base66 + (12836517300623131/4343750000000000000000000000000 : ℝ)*base68 + (24951865286248131/4343750000000000000000000000000 : ℝ)*base70 + (19912842529154381/4343750000000000000000000000000 : ℝ)*base72 + (14116782671337/3475000000000000000000000000 : ℝ)*base74 + (15087392889810631/4343750000000000000000000000000 : ℝ)*base76 + (22491570928779381/4343750000000000000000000000000 : ℝ)*base78 + (18700267493685631/4343750000000000000000000000000 : ℝ)*base80 + (21546144465337/3475000000000000000000000000 : ℝ)*base82 + (3436413/312500000000000000000 : ℝ)*base90 + (3436413/312500000000000000000 : ℝ)*base92 + (3436413/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26474234835709111014106899/2171875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1520268163/100000000000000 : ℝ)*(base19) + (207552297/12500000000000 : ℝ)*(base23) + (92055011/20000000000000 : ℝ)*(lower1) + (261336799/100000000000000 : ℝ)*(upper3) + (50554341/100000000000000 : ℝ)*(lower4) + (246545609/100000000000000 : ℝ)*(upper5) + (100413991374607/6250000000000 : ℝ)*(major0) + (100413991374607/6250000000000 : ℝ)*(major1) + (100413991374607/6250000000000 : ℝ)*(major2) + (31366931/12500000000000 : ℝ)*(sp2) + (153522841045209/6250000000000 : ℝ)*(sp4) + (122818196822759/5000000000000 : ℝ)*(sp5) + (30704544317119/1250000000000 : ℝ)*(sp6) + (756881860944877/100000000000000 : ℝ)*(sp7) + (756881860944877/100000000000000 : ℝ)*(f.failure) + (153522841045209/6250000000000 : ℝ)*(f.sum) + (6293399968173/11293750000000000000000000000 : ℝ)*base66 + (193030483775958229/56468750000000000000000000000000 : ℝ)*base67 + (191034756187479271/56468750000000000000000000000000 : ℝ)*base70 + (1340025954870323021/56468750000000000000000000000000 : ℝ)*base72 + (6504608510567/45175000000000000000000000000 : ℝ)*base74 + (3147244674771479271/56468750000000000000000000000000 : ℝ)*base76 + (527001674410698021/56468750000000000000000000000000 : ℝ)*base78 + (64848063838958229/56468750000000000000000000000000 : ℝ)*base79 + (40409758641683/45175000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5532569/1250000000000000000000 : ℝ)*base89 + (5532569/1250000000000000000000 : ℝ)*base91 + (5532569/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1747_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26533597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3607/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/100 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9001/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9017/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1747_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1747_box_0 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-52959979/625000000 : ℝ)*x 0 + (108571611/200000000 : ℝ)*x 1 + (135714507/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52959979/625000000 : ℝ)^5727 ≤ (247538290259/5000000000000 : ℝ)^4703 := by
    have hnat : (52959979 : ℕ)^5727*5000000000000^4703 ≤ 247538290259^4703*625000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52959979 625000000 247538290259 5000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108571611/200000000 : ℝ)^5727 ≤ (23762309264499/50000000000000 : ℝ)^4703 := by
    have hnat : (108571611 : ℕ)^5727*50000000000000^4703 ≤ 23762309264499^4703*200000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108571611 200000000 23762309264499 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135714507/250000000 : ℝ)^5727 ≤ (47524615650617/100000000000000 : ℝ)^4703 := by
    have hnat : (135714507 : ℕ)^5727*100000000000000^4703 ≤ 47524615650617^4703*250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135714507 250000000 47524615650617 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52959979/625000000 : ℝ), (108571611/200000000 : ℝ), (135714507/250000000 : ℝ)] ![(247538290259/5000000000000 : ℝ), (23762309264499/50000000000000 : ℝ), (47524615650617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52959979/625000000 : ℝ)|^5727 ≤ (247538290259/5000000000000 : ℝ)^4703
        have hw : |(-52959979/625000000 : ℝ)|=(52959979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108571611/200000000 : ℝ)|^5727 ≤ (23762309264499/50000000000000 : ℝ)^4703
        have hw : |(108571611/200000000 : ℝ)|=(108571611/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135714507/250000000 : ℝ)|^5727 ≤ (47524615650617/100000000000000 : ℝ)^4703
        have hw : |(135714507/250000000 : ℝ)|=(135714507/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_box_1 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597342021/5000000000 : ℝ)*x 0 + (-1182973427/10000000000 : ℝ)*x 1 + (2714290207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597342021/5000000000 : ℝ)^5727 ≤ (45042954793057/100000000000000 : ℝ)^4703 := by
    have hnat : (2597342021 : ℕ)^5727*100000000000000^4703 ≤ 45042954793057^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597342021 5000000000 45042954793057 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1182973427/10000000000 : ℝ)^5727 ≤ (7432428111291/100000000000000 : ℝ)^4703 := by
    have hnat : (1182973427 : ℕ)^5727*100000000000000^4703 ≤ 7432428111291^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182973427 10000000000 7432428111291 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714290207/5000000000 : ℝ)^5727 ≤ (47524617079147/100000000000000 : ℝ)^4703 := by
    have hnat : (2714290207 : ℕ)^5727*100000000000000^4703 ≤ 47524617079147^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714290207 5000000000 47524617079147 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597342021/5000000000 : ℝ), (-1182973427/10000000000 : ℝ), (2714290207/5000000000 : ℝ)] ![(45042954793057/100000000000000 : ℝ), (7432428111291/100000000000000 : ℝ), (47524617079147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597342021/5000000000 : ℝ)|^5727 ≤ (45042954793057/100000000000000 : ℝ)^4703
        have hw : |(2597342021/5000000000 : ℝ)|=(2597342021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1182973427/10000000000 : ℝ)|^5727 ≤ (7432428111291/100000000000000 : ℝ)^4703
        have hw : |(-1182973427/10000000000 : ℝ)|=(1182973427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714290207/5000000000 : ℝ)|^5727 ≤ (47524617079147/100000000000000 : ℝ)^4703
        have hw : |(2714290207/5000000000 : ℝ)|=(2714290207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_box_2 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649335491/1250000000 : ℝ)*x 0 + (678572541/1250000000 : ℝ)*x 1 + (-147871713/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649335491/1250000000 : ℝ)^5727 ≤ (45042953589339/100000000000000 : ℝ)^4703 := by
    have hnat : (649335491 : ℕ)^5727*100000000000000^4703 ≤ 45042953589339^4703*1250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649335491 1250000000 45042953589339 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678572541/1250000000 : ℝ)^5727 ≤ (47524616162329/100000000000000 : ℝ)^4703 := by
    have hnat : (678572541 : ℕ)^5727*100000000000000^4703 ≤ 47524616162329^4703*1250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678572541 1250000000 47524616162329 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147871713/1250000000 : ℝ)^5727 ≤ (929053778821/12500000000000 : ℝ)^4703 := by
    have hnat : (147871713 : ℕ)^5727*12500000000000^4703 ≤ 929053778821^4703*1250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147871713 1250000000 929053778821 12500000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649335491/1250000000 : ℝ), (678572541/1250000000 : ℝ), (-147871713/1250000000 : ℝ)] ![(45042953589339/100000000000000 : ℝ), (47524616162329/100000000000000 : ℝ), (929053778821/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649335491/1250000000 : ℝ)|^5727 ≤ (45042953589339/100000000000000 : ℝ)^4703
        have hw : |(649335491/1250000000 : ℝ)|=(649335491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678572541/1250000000 : ℝ)|^5727 ≤ (47524616162329/100000000000000 : ℝ)^4703
        have hw : |(678572541/1250000000 : ℝ)|=(678572541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147871713/1250000000 : ℝ)|^5727 ≤ (929053778821/12500000000000 : ℝ)^4703
        have hw : |(-147871713/1250000000 : ℝ)|=(147871713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_box_3 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (28463017/62500000 : ℝ)*x 0 + (1901631697/5000000000 : ℝ)*x 1 + (1901632073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28463017/62500000 : ℝ)^5727 ≤ (2398299489599/6250000000000 : ℝ)^4703 := by
    have hnat : (28463017 : ℕ)^5727*6250000000000^4703 ≤ 2398299489599^4703*62500000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28463017 62500000 2398299489599 6250000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1901631697/5000000000 : ℝ)^5727 ≤ (30813600366419/100000000000000 : ℝ)^4703 := by
    have hnat : (1901631697 : ℕ)^5727*100000000000000^4703 ≤ 30813600366419^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901631697 5000000000 30813600366419 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1901632073/5000000000 : ℝ)^5727 ≤ (15406803892801/50000000000000 : ℝ)^4703 := by
    have hnat : (1901632073 : ℕ)^5727*50000000000000^4703 ≤ 15406803892801^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901632073 5000000000 15406803892801 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(28463017/62500000 : ℝ), (1901631697/5000000000 : ℝ), (1901632073/5000000000 : ℝ)] ![(2398299489599/6250000000000 : ℝ), (30813600366419/100000000000000 : ℝ), (15406803892801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(28463017/62500000 : ℝ)|^5727 ≤ (2398299489599/6250000000000 : ℝ)^4703
        have hw : |(28463017/62500000 : ℝ)|=(28463017/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1901631697/5000000000 : ℝ)|^5727 ≤ (30813600366419/100000000000000 : ℝ)^4703
        have hw : |(1901631697/5000000000 : ℝ)|=(1901631697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1901632073/5000000000 : ℝ)|^5727 ≤ (15406803892801/50000000000000 : ℝ)^4703
        have hw : |(1901632073/5000000000 : ℝ)|=(1901632073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_box_4 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-208847493/1250000000 : ℝ)*x 0 + (5128169389/10000000000 : ℝ)*x 1 + (5128168783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208847493/1250000000 : ℝ)^5727 ≤ (2829194849409/25000000000000 : ℝ)^4703 := by
    have hnat : (208847493 : ℕ)^5727*25000000000000^4703 ≤ 2829194849409^4703*1250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208847493 1250000000 2829194849409 25000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128169389/10000000000 : ℝ)^5727 ≤ (8868322697423/20000000000000 : ℝ)^4703 := by
    have hnat : (5128169389 : ℕ)^5727*20000000000000^4703 ≤ 8868322697423^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128169389 10000000000 8868322697423 20000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5128168783/10000000000 : ℝ)^5727 ≤ (11085401776583/25000000000000 : ℝ)^4703 := by
    have hnat : (5128168783 : ℕ)^5727*25000000000000^4703 ≤ 11085401776583^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128168783 10000000000 11085401776583 25000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208847493/1250000000 : ℝ), (5128169389/10000000000 : ℝ), (5128168783/10000000000 : ℝ)] ![(2829194849409/25000000000000 : ℝ), (8868322697423/20000000000000 : ℝ), (11085401776583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208847493/1250000000 : ℝ)|^5727 ≤ (2829194849409/25000000000000 : ℝ)^4703
        have hw : |(-208847493/1250000000 : ℝ)|=(208847493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128169389/10000000000 : ℝ)|^5727 ≤ (8868322697423/20000000000000 : ℝ)^4703
        have hw : |(5128169389/10000000000 : ℝ)|=(5128169389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5128168783/10000000000 : ℝ)|^5727 ≤ (11085401776583/25000000000000 : ℝ)^4703
        have hw : |(5128168783/10000000000 : ℝ)|=(5128168783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_box_5 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396042023/10000000000 : ℝ)*x 0 + (-659157287/5000000000 : ℝ)*x 1 + (5128168857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396042023/10000000000 : ℝ)^5727 ≤ (9435592538711/20000000000000 : ℝ)^4703 := by
    have hnat : (5396042023 : ℕ)^5727*20000000000000^4703 ≤ 9435592538711^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396042023 10000000000 9435592538711 20000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659157287/5000000000 : ℝ)^5727 ≤ (8480429409871/100000000000000 : ℝ)^4703 := by
    have hnat : (659157287 : ℕ)^5727*100000000000000^4703 ≤ 8480429409871^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659157287 5000000000 8480429409871 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5128168857/10000000000 : ℝ)^5727 ≤ (44341607885503/100000000000000 : ℝ)^4703 := by
    have hnat : (5128168857 : ℕ)^5727*100000000000000^4703 ≤ 44341607885503^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128168857 10000000000 44341607885503 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396042023/10000000000 : ℝ), (-659157287/5000000000 : ℝ), (5128168857/10000000000 : ℝ)] ![(9435592538711/20000000000000 : ℝ), (8480429409871/100000000000000 : ℝ), (44341607885503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396042023/10000000000 : ℝ)|^5727 ≤ (9435592538711/20000000000000 : ℝ)^4703
        have hw : |(5396042023/10000000000 : ℝ)|=(5396042023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-659157287/5000000000 : ℝ)|^5727 ≤ (8480429409871/100000000000000 : ℝ)^4703
        have hw : |(-659157287/5000000000 : ℝ)|=(659157287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5128168857/10000000000 : ℝ)|^5727 ≤ (44341607885503/100000000000000 : ℝ)^4703
        have hw : |(5128168857/10000000000 : ℝ)|=(5128168857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_box_6 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1349010477/2500000000 : ℝ)*x 0 + (5128169239/10000000000 : ℝ)*x 1 + (-1318314217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1349010477/2500000000 : ℝ)^5727 ≤ (23588980734591/50000000000000 : ℝ)^4703 := by
    have hnat : (1349010477 : ℕ)^5727*50000000000000^4703 ≤ 23588980734591^4703*2500000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349010477 2500000000 23588980734591 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128169239/10000000000 : ℝ)^5727 ≤ (44341611907713/100000000000000 : ℝ)^4703 := by
    have hnat : (5128169239 : ℕ)^5727*100000000000000^4703 ≤ 44341611907713^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128169239 10000000000 44341611907713 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318314217/10000000000 : ℝ)^5727 ≤ (8480426613343/100000000000000 : ℝ)^4703 := by
    have hnat : (1318314217 : ℕ)^5727*100000000000000^4703 ≤ 8480426613343^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318314217 10000000000 8480426613343 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1349010477/2500000000 : ℝ), (5128169239/10000000000 : ℝ), (-1318314217/10000000000 : ℝ)] ![(23588980734591/50000000000000 : ℝ), (44341611907713/100000000000000 : ℝ), (8480426613343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1349010477/2500000000 : ℝ)|^5727 ≤ (23588980734591/50000000000000 : ℝ)^4703
        have hw : |(1349010477/2500000000 : ℝ)|=(1349010477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128169239/10000000000 : ℝ)|^5727 ≤ (44341611907713/100000000000000 : ℝ)^4703
        have hw : |(5128169239/10000000000 : ℝ)|=(5128169239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1318314217/10000000000 : ℝ)|^5727 ≤ (8480426613343/100000000000000 : ℝ)^4703
        have hw : |(-1318314217/10000000000 : ℝ)|=(1318314217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_box_7 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (43302207/125000000 : ℝ)*x 0 + (1086519613/2500000000 : ℝ)*x 1 + (4346078473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43302207/125000000 : ℝ)^5727 ≤ (27501449413381/100000000000000 : ℝ)^4703 := by
    have hnat : (43302207 : ℕ)^5727*100000000000000^4703 ≤ 27501449413381^4703*125000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43302207 125000000 27501449413381 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086519613/2500000000 : ℝ)^5727 ≤ (18124637589869/50000000000000 : ℝ)^4703 := by
    have hnat : (1086519613 : ℕ)^5727*50000000000000^4703 ≤ 18124637589869^4703*2500000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086519613 2500000000 18124637589869 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4346078473/10000000000 : ℝ)^5727 ≤ (36249275393029/100000000000000 : ℝ)^4703 := by
    have hnat : (4346078473 : ℕ)^5727*100000000000000^4703 ≤ 36249275393029^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346078473 10000000000 36249275393029 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43302207/125000000 : ℝ), (1086519613/2500000000 : ℝ), (4346078473/10000000000 : ℝ)] ![(27501449413381/100000000000000 : ℝ), (18124637589869/50000000000000 : ℝ), (36249275393029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43302207/125000000 : ℝ)|^5727 ≤ (27501449413381/100000000000000 : ℝ)^4703
        have hw : |(43302207/125000000 : ℝ)|=(43302207/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086519613/2500000000 : ℝ)|^5727 ≤ (18124637589869/50000000000000 : ℝ)^4703
        have hw : |(1086519613/2500000000 : ℝ)|=(1086519613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4346078473/10000000000 : ℝ)|^5727 ≤ (36249275393029/100000000000000 : ℝ)^4703
        have hw : |(4346078473/10000000000 : ℝ)|=(4346078473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_box_8 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1491795493/10000000000 : ℝ)*x 0 + (195989879/400000000 : ℝ)*x 1 + (68640573/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1491795493/10000000000 : ℝ)^5727 ≤ (9858213895151/100000000000000 : ℝ)^4703 := by
    have hnat : (1491795493 : ℕ)^5727*100000000000000^4703 ≤ 9858213895151^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491795493 10000000000 9858213895151 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195989879/400000000 : ℝ)^5727 ≤ (10487069113263/25000000000000 : ℝ)^4703 := by
    have hnat : (195989879 : ℕ)^5727*25000000000000^4703 ≤ 10487069113263^4703*400000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195989879 400000000 10487069113263 25000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68640573/125000000 : ℝ)^5727 ≤ (48193509632063/100000000000000 : ℝ)^4703 := by
    have hnat : (68640573 : ℕ)^5727*100000000000000^4703 ≤ 48193509632063^4703*125000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68640573 125000000 48193509632063 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1491795493/10000000000 : ℝ), (195989879/400000000 : ℝ), (68640573/125000000 : ℝ)] ![(9858213895151/100000000000000 : ℝ), (10487069113263/25000000000000 : ℝ), (48193509632063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1491795493/10000000000 : ℝ)|^5727 ≤ (9858213895151/100000000000000 : ℝ)^4703
        have hw : |(-1491795493/10000000000 : ℝ)|=(1491795493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195989879/400000000 : ℝ)|^5727 ≤ (10487069113263/25000000000000 : ℝ)^4703
        have hw : |(195989879/400000000 : ℝ)|=(195989879/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68640573/125000000 : ℝ)|^5727 ≤ (48193509632063/100000000000000 : ℝ)^4703
        have hw : |(68640573/125000000 : ℝ)|=(68640573/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_box_9 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (322046469/625000000 : ℝ)*x 0 + (-1153292409/10000000000 : ℝ)*x 1 + (5491248117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (322046469/625000000 : ℝ)^5727 ≤ (44600497627267/100000000000000 : ℝ)^4703 := by
    have hnat : (322046469 : ℕ)^5727*100000000000000^4703 ≤ 44600497627267^4703*625000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322046469 625000000 44600497627267 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1153292409/10000000000 : ℝ)^5727 ≤ (7205968393259/100000000000000 : ℝ)^4703 := by
    have hnat : (1153292409 : ℕ)^5727*100000000000000^4703 ≤ 7205968393259^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153292409 10000000000 7205968393259 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5491248117/10000000000 : ℝ)^5727 ≤ (48193533967151/100000000000000 : ℝ)^4703 := by
    have hnat : (5491248117 : ℕ)^5727*100000000000000^4703 ≤ 48193533967151^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491248117 10000000000 48193533967151 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(322046469/625000000 : ℝ), (-1153292409/10000000000 : ℝ), (5491248117/10000000000 : ℝ)] ![(44600497627267/100000000000000 : ℝ), (7205968393259/100000000000000 : ℝ), (48193533967151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(322046469/625000000 : ℝ)|^5727 ≤ (44600497627267/100000000000000 : ℝ)^4703
        have hw : |(322046469/625000000 : ℝ)|=(322046469/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1153292409/10000000000 : ℝ)|^5727 ≤ (7205968393259/100000000000000 : ℝ)^4703
        have hw : |(-1153292409/10000000000 : ℝ)|=(1153292409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5491248117/10000000000 : ℝ)|^5727 ≤ (48193533967151/100000000000000 : ℝ)^4703
        have hw : |(5491248117/10000000000 : ℝ)|=(5491248117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_box_10 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1030548863/2000000000 : ℝ)*x 0 + (5491247507/10000000000 : ℝ)*x 1 + (-1153292141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1030548863/2000000000 : ℝ)^5727 ≤ (22300253087729/50000000000000 : ℝ)^4703 := by
    have hnat : (1030548863 : ℕ)^5727*50000000000000^4703 ≤ 22300253087729^4703*2000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030548863 2000000000 22300253087729 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5491247507/10000000000 : ℝ)^5727 ≤ (48193527447869/100000000000000 : ℝ)^4703 := by
    have hnat : (5491247507 : ℕ)^5727*100000000000000^4703 ≤ 48193527447869^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491247507 10000000000 48193527447869 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1153292141/10000000000 : ℝ)^5727 ≤ (7205966354153/100000000000000 : ℝ)^4703 := by
    have hnat : (1153292141 : ℕ)^5727*100000000000000^4703 ≤ 7205966354153^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153292141 10000000000 7205966354153 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1030548863/2000000000 : ℝ), (5491247507/10000000000 : ℝ), (-1153292141/10000000000 : ℝ)] ![(22300253087729/50000000000000 : ℝ), (48193527447869/100000000000000 : ℝ), (7205966354153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1030548863/2000000000 : ℝ)|^5727 ≤ (22300253087729/50000000000000 : ℝ)^4703
        have hw : |(1030548863/2000000000 : ℝ)|=(1030548863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5491247507/10000000000 : ℝ)|^5727 ≤ (48193527447869/100000000000000 : ℝ)^4703
        have hw : |(5491247507/10000000000 : ℝ)|=(5491247507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1153292141/10000000000 : ℝ)|^5727 ≤ (7205966354153/100000000000000 : ℝ)^4703
        have hw : |(-1153292141/10000000000 : ℝ)|=(1153292141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_box_11 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4770824823/10000000000 : ℝ)*x 0 + (92240193/250000000 : ℝ)*x 1 + (1844803661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4770824823/10000000000 : ℝ)^5727 ≤ (5076011052761/12500000000000 : ℝ)^4703 := by
    have hnat : (4770824823 : ℕ)^5727*12500000000000^4703 ≤ 5076011052761^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770824823 10000000000 5076011052761 12500000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92240193/250000000 : ℝ)^5727 ≤ (29695957729813/100000000000000 : ℝ)^4703 := by
    have hnat : (92240193 : ℕ)^5727*100000000000000^4703 ≤ 29695957729813^4703*250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92240193 250000000 29695957729813 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1844803661/5000000000 : ℝ)^5727 ≤ (927998557157/3125000000000 : ℝ)^4703 := by
    have hnat : (1844803661 : ℕ)^5727*3125000000000^4703 ≤ 927998557157^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844803661 5000000000 927998557157 3125000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4770824823/10000000000 : ℝ), (92240193/250000000 : ℝ), (1844803661/5000000000 : ℝ)] ![(5076011052761/12500000000000 : ℝ), (29695957729813/100000000000000 : ℝ), (927998557157/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4770824823/10000000000 : ℝ)|^5727 ≤ (5076011052761/12500000000000 : ℝ)^4703
        have hw : |(4770824823/10000000000 : ℝ)|=(4770824823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(92240193/250000000 : ℝ)|^5727 ≤ (29695957729813/100000000000000 : ℝ)^4703
        have hw : |(92240193/250000000 : ℝ)|=(92240193/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1844803661/5000000000 : ℝ)|^5727 ≤ (927998557157/3125000000000 : ℝ)^4703
        have hw : |(1844803661/5000000000 : ℝ)|=(1844803661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_box_12 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-50640689/500000000 : ℝ)*x 0 + (5643424701/10000000000 : ℝ)*x 1 + (637241741/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50640689/500000000 : ℝ)^5727 ≤ (768971478003/12500000000000 : ℝ)^4703 := by
    have hnat : (50640689 : ℕ)^5727*12500000000000^4703 ≤ 768971478003^4703*500000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50640689 500000000 768971478003 12500000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5643424701/10000000000 : ℝ)^5727 ≤ (6228096200111/12500000000000 : ℝ)^4703 := by
    have hnat : (5643424701 : ℕ)^5727*12500000000000^4703 ≤ 6228096200111^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5643424701 10000000000 6228096200111 12500000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637241741/1250000000 : ℝ)^5727 ≤ (11005864641041/25000000000000 : ℝ)^4703 := by
    have hnat : (637241741 : ℕ)^5727*25000000000000^4703 ≤ 11005864641041^4703*1250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637241741 1250000000 11005864641041 25000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50640689/500000000 : ℝ), (5643424701/10000000000 : ℝ), (637241741/1250000000 : ℝ)] ![(768971478003/12500000000000 : ℝ), (6228096200111/12500000000000 : ℝ), (11005864641041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50640689/500000000 : ℝ)|^5727 ≤ (768971478003/12500000000000 : ℝ)^4703
        have hw : |(-50640689/500000000 : ℝ)|=(50640689/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5643424701/10000000000 : ℝ)|^5727 ≤ (6228096200111/12500000000000 : ℝ)^4703
        have hw : |(5643424701/10000000000 : ℝ)|=(5643424701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(637241741/1250000000 : ℝ)|^5727 ≤ (11005864641041/25000000000000 : ℝ)^4703
        have hw : |(637241741/1250000000 : ℝ)|=(637241741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_box_13 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2708190051/5000000000 : ℝ)*x 0 + (-665632377/5000000000 : ℝ)*x 1 + (5097931483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708190051/5000000000 : ℝ)^5727 ≤ (23697292701857/50000000000000 : ℝ)^4703 := by
    have hnat : (2708190051 : ℕ)^5727*50000000000000^4703 ≤ 23697292701857^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708190051 5000000000 23697292701857 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (665632377/5000000000 : ℝ)^5727 ≤ (8581981721809/100000000000000 : ℝ)^4703 := by
    have hnat : (665632377 : ℕ)^5727*100000000000000^4703 ≤ 8581981721809^4703*5000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665632377 5000000000 8581981721809 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5097931483/10000000000 : ℝ)^5727 ≤ (11005858213261/25000000000000 : ℝ)^4703 := by
    have hnat : (5097931483 : ℕ)^5727*25000000000000^4703 ≤ 11005858213261^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097931483 10000000000 11005858213261 25000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708190051/5000000000 : ℝ), (-665632377/5000000000 : ℝ), (5097931483/10000000000 : ℝ)] ![(23697292701857/50000000000000 : ℝ), (8581981721809/100000000000000 : ℝ), (11005858213261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708190051/5000000000 : ℝ)|^5727 ≤ (23697292701857/50000000000000 : ℝ)^4703
        have hw : |(2708190051/5000000000 : ℝ)|=(2708190051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-665632377/5000000000 : ℝ)|^5727 ≤ (8581981721809/100000000000000 : ℝ)^4703
        have hw : |(-665632377/5000000000 : ℝ)|=(665632377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5097931483/10000000000 : ℝ)|^5727 ≤ (11005858213261/25000000000000 : ℝ)^4703
        have hw : |(5097931483/10000000000 : ℝ)|=(5097931483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_box_14 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5416380449/10000000000 : ℝ)*x 0 + (254896587/500000000 : ℝ)*x 1 + (-1331263939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416380449/10000000000 : ℝ)^5727 ≤ (11848647275289/25000000000000 : ℝ)^4703 := by
    have hnat : (5416380449 : ℕ)^5727*25000000000000^4703 ≤ 11848647275289^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416380449 10000000000 11848647275289 25000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254896587/500000000 : ℝ)^5727 ≤ (44023435555603/100000000000000 : ℝ)^4703 := by
    have hnat : (254896587 : ℕ)^5727*100000000000000^4703 ≤ 44023435555603^4703*500000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254896587 500000000 44023435555603 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1331263939/10000000000 : ℝ)^5727 ≤ (343279012959/4000000000000 : ℝ)^4703 := by
    have hnat : (1331263939 : ℕ)^5727*4000000000000^4703 ≤ 343279012959^4703*10000000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331263939 10000000000 343279012959 4000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416380449/10000000000 : ℝ), (254896587/500000000 : ℝ), (-1331263939/10000000000 : ℝ)] ![(11848647275289/25000000000000 : ℝ), (44023435555603/100000000000000 : ℝ), (343279012959/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416380449/10000000000 : ℝ)|^5727 ≤ (11848647275289/25000000000000 : ℝ)^4703
        have hw : |(5416380449/10000000000 : ℝ)|=(5416380449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(254896587/500000000 : ℝ)|^5727 ≤ (44023435555603/100000000000000 : ℝ)^4703
        have hw : |(254896587/500000000 : ℝ)|=(254896587/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1331263939/10000000000 : ℝ)|^5727 ≤ (343279012959/4000000000000 : ℝ)^4703
        have hw : |(-1331263939/10000000000 : ℝ)|=(1331263939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1747_box_15 (p : ℝ) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209328809/625000000 : ℝ)*x 0 + (550061451/1250000000 : ℝ)*x 1 + (137515553/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209328809/625000000 : ℝ)^5727 ≤ (13197283161541/50000000000000 : ℝ)^4703 := by
    have hnat : (209328809 : ℕ)^5727*50000000000000^4703 ≤ 13197283161541^4703*625000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209328809 625000000 13197283161541 50000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550061451/1250000000 : ℝ)^5727 ≤ (9200671458031/25000000000000 : ℝ)^4703 := by
    have hnat : (550061451 : ℕ)^5727*25000000000000^4703 ≤ 9200671458031^4703*1250000000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550061451 1250000000 9200671458031 25000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137515553/312500000 : ℝ)^5727 ≤ (36802747834057/100000000000000 : ℝ)^4703 := by
    have hnat : (137515553 : ℕ)^5727*100000000000000^4703 ≤ 36802747834057^4703*312500000^5727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137515553 312500000 36802747834057 100000000000000 5727 4703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5727/1024 : ℝ)) 5727 4703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209328809/625000000 : ℝ), (550061451/1250000000 : ℝ), (137515553/312500000 : ℝ)] ![(13197283161541/50000000000000 : ℝ), (9200671458031/25000000000000 : ℝ), (36802747834057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209328809/625000000 : ℝ)|^5727 ≤ (13197283161541/50000000000000 : ℝ)^4703
        have hw : |(209328809/625000000 : ℝ)|=(209328809/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550061451/1250000000 : ℝ)|^5727 ≤ (9200671458031/25000000000000 : ℝ)^4703
        have hw : |(550061451/1250000000 : ℝ)|=(550061451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137515553/312500000 : ℝ)|^5727 ≤ (36802747834057/100000000000000 : ℝ)^4703
        have hw : |(137515553/312500000 : ℝ)|=(137515553/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1747_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26533597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(68857/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57963/100000 : ℝ) ∧ (8139/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (92843/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9001/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9001/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9001/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9001/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9001/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9001/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9001/100000 : ℝ) ^ (5711/1024 : ℝ) ≤ (147205608061071/100000000000000000000 : ℝ) := by
    have hpowers : (9001/100000 : ℝ)^5711 ≤ (147205608061071/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9001 : ℕ)^5711*100000000000000000000^1024 ≤ 147205608061071^1024*100000^5711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9001 100000 147205608061071 100000000000000000000 5711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9001/100000 : ℝ)) (X := (147205608061071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9017/50000 : ℝ) ^ (5711/1024 : ℝ) ≤ (7097657272504423/100000000000000000000 : ℝ) := by
    have hpowers : (9017/50000 : ℝ)^5711 ≤ (7097657272504423/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9017 : ℕ)^5711*100000000000000000000^1024 ≤ 7097657272504423^1024*50000^5711 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9017 50000 7097657272504423 100000000000000000000 5711 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9017/50000 : ℝ)) (X := (7097657272504423/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000147205608061071/50000000000000000000 : ℝ) ≤ (5000002639438987/5000000000000000 : ℝ) ^ (5711/1024 : ℝ) := by
    have hpowers : (50000147205608061071/50000000000000000000 : ℝ)^1024 ≤ (5000002639438987/5000000000000000 : ℝ)^5711 := by
      have hnat : (50000147205608061071 : ℕ)^1024*5000000000000000^5711 ≤ 5000002639438987^5711*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000147205608061071 50000000000000000000 5000002639438987 5000000000000000 1024 5711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000002639438987/5000000000000000 : ℝ)) (X := (50000147205608061071/50000000000000000000 : ℝ)) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50003622431440282747/50000000000000000000 : ℝ) ≤ (10000129898775107/10000000000000000 : ℝ) ^ (5711/1024 : ℝ) := by
    have hpowers : (50003622431440282747/50000000000000000000 : ℝ)^1024 ≤ (10000129898775107/10000000000000000 : ℝ)^5711 := by
      have hnat : (50003622431440282747 : ℕ)^1024*10000000000000000^5711 ≤ 10000129898775107^5711*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003622431440282747 50000000000000000000 10000129898775107 10000000000000000 1024 5711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000129898775107/10000000000000000 : ℝ)) (X := (50003622431440282747/50000000000000000000 : ℝ)) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50007097657272504423/50000000000000000000 : ℝ) ≤ (125003181483403/125000000000000 : ℝ) ^ (5711/1024 : ℝ) := by
    have hpowers : (50007097657272504423/50000000000000000000 : ℝ)^1024 ≤ (125003181483403/125000000000000 : ℝ)^5711 := by
      have hnat : (50007097657272504423 : ℕ)^1024*125000000000000^5711 ≤ 125003181483403^5711*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007097657272504423 50000000000000000000 125003181483403 125000000000000 1024 5711 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125003181483403/125000000000000 : ℝ)) (X := (50007097657272504423/50000000000000000000 : ℝ)) (by norm_num) 5711 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(147205608061071/100000000000000000000 : ℝ) ≤ ((7527317023059712573/7527500000000000000 : ℝ)+2*(41539965711/301100000000000 : ℝ)*(9001/100000 : ℝ))^(5711/1024 : ℝ) := by
    rw [show (7527317023059712573/7527500000000000000 : ℝ)+2*(41539965711/301100000000000 : ℝ)*(9001/100000 : ℝ)=(5000002639438987/5000000000000000 : ℝ) by norm_num, show 1+2*(147205608061071/100000000000000000000 : ℝ)=(50000147205608061071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7097657272504423/100000000000000000000 : ℝ)+(147205608061071/100000000000000000000 : ℝ) ≤ ((7527317023059712573/7527500000000000000 : ℝ)+(41539965711/301100000000000 : ℝ)*((9017/50000 : ℝ)+(9001/100000 : ℝ)))^(5711/1024 : ℝ) := by
    rw [show (7527317023059712573/7527500000000000000 : ℝ)+(41539965711/301100000000000 : ℝ)*((9017/50000 : ℝ)+(9001/100000 : ℝ))=(10000129898775107/10000000000000000 : ℝ) by norm_num, show 1+(7097657272504423/100000000000000000000 : ℝ)+(147205608061071/100000000000000000000 : ℝ)=(50003622431440282747/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7097657272504423/100000000000000000000 : ℝ) ≤ ((7527317023059712573/7527500000000000000 : ℝ)+2*(41539965711/301100000000000 : ℝ)*(9017/50000 : ℝ))^(5711/1024 : ℝ) := by
    rw [show (7527317023059712573/7527500000000000000 : ℝ)+2*(41539965711/301100000000000 : ℝ)*(9017/50000 : ℝ)=(125003181483403/125000000000000 : ℝ) by norm_num, show 1+2*(7097657272504423/100000000000000000000 : ℝ)=(50007097657272504423/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7527317023059712573/7527500000000000000 : ℝ)*(X 1 0+X 2 0)+(41539965711/301100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5711/1024 : ℝ)) (lo := (9001/100000 : ℝ)) (hi := (9017/50000 : ℝ)) (c := (7527317023059712573/7527500000000000000 : ℝ)) (alpha := (41539965711/301100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7527317023059712573/7527500000000000000 : ℝ)*(X 0 1+X 2 1)+(41539965711/301100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5711/1024 : ℝ)) (lo := (9001/100000 : ℝ)) (hi := (9017/50000 : ℝ)) (c := (7527317023059712573/7527500000000000000 : ℝ)) (alpha := (41539965711/301100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7527317023059712573/7527500000000000000 : ℝ)*(X 0 2+X 1 2)+(41539965711/301100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5711/1024 : ℝ)) (lo := (9001/100000 : ℝ)) (hi := (9017/50000 : ℝ)) (c := (7527317023059712573/7527500000000000000 : ℝ)) (alpha := (41539965711/301100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-52959979/625000000 : ℝ)*X 0 0+(108571611/200000000 : ℝ)*X 0 1+(135714507/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2597342021/5000000000 : ℝ)*X 1 0+(-1182973427/10000000000 : ℝ)*X 1 1+(2714290207/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((649335491/1250000000 : ℝ)*X 2 0+(678572541/1250000000 : ℝ)*X 2 1+(-147871713/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((28463017/62500000 : ℝ)*X 0 0+(1901631697/5000000000 : ℝ)*X 0 1+(1901632073/5000000000 : ℝ)*X 0 2+(28463017/62500000 : ℝ)*X 1 0+(1901631697/5000000000 : ℝ)*X 1 1+(1901632073/5000000000 : ℝ)*X 1 2+(28463017/62500000 : ℝ)*X 2 0+(1901631697/5000000000 : ℝ)*X 2 1+(1901632073/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-208847493/1250000000 : ℝ)*X 0 0+(5128169389/10000000000 : ℝ)*X 0 1+(5128168783/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5396042023/10000000000 : ℝ)*X 1 0+(-659157287/5000000000 : ℝ)*X 1 1+(5128168857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1349010477/2500000000 : ℝ)*X 2 0+(5128169239/10000000000 : ℝ)*X 2 1+(-1318314217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((43302207/125000000 : ℝ)*X 0 0+(1086519613/2500000000 : ℝ)*X 0 1+(4346078473/10000000000 : ℝ)*X 0 2+(43302207/125000000 : ℝ)*X 1 0+(1086519613/2500000000 : ℝ)*X 1 1+(4346078473/10000000000 : ℝ)*X 1 2+(43302207/125000000 : ℝ)*X 2 0+(1086519613/2500000000 : ℝ)*X 2 1+(4346078473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1491795493/10000000000 : ℝ)*X 0 0+(195989879/400000000 : ℝ)*X 0 1+(68640573/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((322046469/625000000 : ℝ)*X 1 0+(-1153292409/10000000000 : ℝ)*X 1 1+(5491248117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1030548863/2000000000 : ℝ)*X 2 0+(5491247507/10000000000 : ℝ)*X 2 1+(-1153292141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4770824823/10000000000 : ℝ)*X 0 0+(92240193/250000000 : ℝ)*X 0 1+(1844803661/5000000000 : ℝ)*X 0 2+(4770824823/10000000000 : ℝ)*X 1 0+(92240193/250000000 : ℝ)*X 1 1+(1844803661/5000000000 : ℝ)*X 1 2+(4770824823/10000000000 : ℝ)*X 2 0+(92240193/250000000 : ℝ)*X 2 1+(1844803661/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-50640689/500000000 : ℝ)*X 0 0+(5643424701/10000000000 : ℝ)*X 0 1+(637241741/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2708190051/5000000000 : ℝ)*X 1 0+(-665632377/5000000000 : ℝ)*X 1 1+(5097931483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5416380449/10000000000 : ℝ)*X 2 0+(254896587/500000000 : ℝ)*X 2 1+(-1331263939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((209328809/625000000 : ℝ)*X 0 0+(550061451/1250000000 : ℝ)*X 0 1+(137515553/312500000 : ℝ)*X 0 2+(209328809/625000000 : ℝ)*X 1 0+(550061451/1250000000 : ℝ)*X 1 1+(137515553/312500000 : ℝ)*X 1 2+(209328809/625000000 : ℝ)*X 2 0+(550061451/1250000000 : ℝ)*X 2 1+(137515553/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1747_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-68857/100000 : ℝ) ≤ (-129575244108320626326718974483147/188187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1348977/20000000000000 : ℝ)*(lower1) + (11537259/6250000000000 : ℝ)*(lower2) + (17470049/25000000000000 : ℝ)*(lower3) + (154790359/100000000000000 : ℝ)*(lower4) + (24414359/50000000000000 : ℝ)*(lower5) + (519677891596213/50000000000000 : ℝ)*(major0) + (519677891596213/50000000000000 : ℝ)*(major1) + (519677891596213/50000000000000 : ℝ)*(major2) + (806009776804743/50000000000000 : ℝ)*(sp4) + (403005405264217/25000000000000 : ℝ)*(sp5) + (1611997851390721/100000000000000 : ℝ)*(sp6) + (30602586811697/6250000000000 : ℝ)*(sp7) + (2067447381/100000000000000 : ℝ)*(sp8) + (23769666147/100000000000000 : ℝ)*(sp14) + (30602586811697/6250000000000 : ℝ)*(f.failure) + (403005405264217/25000000000000 : ℝ)*(f.sum) + (30596231137779/15055000000000000000000000000 : ℝ)*base66 + (2044586716945986049/376375000000000000000000000000000 : ℝ)*base67 + (3337884895739611049/376375000000000000000000000000000 : ℝ)*base69 + (1663130775224138951/376375000000000000000000000000000 : ℝ)*base72 + (14942064585537/7527500000000000000000000000 : ℝ)*base74 + (1647758167454861049/376375000000000000000000000000000 : ℝ)*base75 + (946829728553736049/376375000000000000000000000000000 : ℝ)*base77 + (667342158837763951/376375000000000000000000000000000 : ℝ)*base80 + (32990895104389/3763750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (271609/78125000000000000000 : ℝ)*base89 + (271609/78125000000000000000 : ℝ)*base91 + (271609/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (57963/100000 : ℝ) ≤ (43633471571916906001619014466817/75275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13534197/100000000000000 : ℝ)*(upper0) + (27534791/50000000000000 : ℝ)*(upper2) + (198721/100000000000000 : ℝ)*(upper4) + (191709/6250000000000 : ℝ)*(upper5) + (232221448922381/20000000000000 : ℝ)*(major0) + (232221448922381/20000000000000 : ℝ)*(major1) + (232221448922381/20000000000000 : ℝ)*(major2) + (877947038164211/50000000000000 : ℝ)*(sp0) + (87794664655177/5000000000000 : ℝ)*(sp1) + (351177905252003/20000000000000 : ℝ)*(sp2) + (546998107162549/100000000000000 : ℝ)*(sp3) + (391612441/50000000000000 : ℝ)*(sp5) + (4550068407/100000000000000 : ℝ)*(sp10) + (498328023/100000000000000 : ℝ)*(sp11) + (136749651372643/25000000000000 : ℝ)*(f.failure) + (877947038164211/50000000000000 : ℝ)*(f.sum) + (106970811289/37637500000000000000000000 : ℝ)*base66 + (559456765037228687/150550000000000000000000000000000 : ℝ)*base68 + (589688673501928687/150550000000000000000000000000000 : ℝ)*base70 + (1016365809102178687/150550000000000000000000000000000 : ℝ)*base72 + (12532857446693/3011000000000000000000000000 : ℝ)*base73 + (581445650602628687/150550000000000000000000000000000 : ℝ)*base76 + (455863666539628687/150550000000000000000000000000000 : ℝ)*base78 + (14285732680178687/150550000000000000000000000000000 : ℝ)*base80 + (686397663713/752750000000000000000000000 : ℝ)*base82 + (3061871/312500000000000000000 : ℝ)*base89 + (3061871/312500000000000000000 : ℝ)*base91 + (3061871/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (8139/10000 : ℝ) ≤ (153171016106809394890151359943829/188187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29687357/100000000000000 : ℝ)*(lower1) + (9009713/100000000000000 : ℝ)*(lower3) + (29169533/25000000000000 : ℝ)*(upper4) + (561762537430603/50000000000000 : ℝ)*(major0) + (561762537430603/50000000000000 : ℝ)*(major1) + (561762537430603/50000000000000 : ℝ)*(major2) + (1104057361/25000000000000 : ℝ)*(sp0) + (31272277079/50000000000000 : ℝ)*(sp1) + (14418565339/25000000000000 : ℝ)*(sp2) + (15716104793/100000000000000 : ℝ)*(sp3) + (1690621197161663/100000000000000 : ℝ)*(sp8) + (422640767209237/25000000000000 : ℝ)*(sp9) + (1690567939129751/100000000000000 : ℝ)*(sp10) + (66159737176673/12500000000000 : ℝ)*(sp11) + (264646806759089/50000000000000 : ℝ)*(f.failure) + (845312806695553/50000000000000 : ℝ)*(f.sum) + (70434102655031/15055000000000000000000000000 : ℝ)*base65 + (535257097705271519/376375000000000000000000000000000 : ℝ)*base67 + (11102271222916646519/376375000000000000000000000000000 : ℝ)*base69 + (3570520159879896519/376375000000000000000000000000000 : ℝ)*base71 + (7067901793823/7527500000000000000000000000 : ℝ)*base73 + (2386897063295646519/376375000000000000000000000000000 : ℝ)*base75 + (338298412435521519/376375000000000000000000000000000 : ℝ)*base77 + (108240126342771519/376375000000000000000000000000000 : ℝ)*base79 + (98070512047361/15055000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (6113133/625000000000000000000 : ℝ)*base89 + (6113133/625000000000000000000 : ℝ)*base91 + (6113133/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-92843/100000 : ℝ) ≤ (-17471455866149382833438735720277/18818750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47023881/50000000000000 : ℝ)*(lower3) + (72548201/100000000000000 : ℝ)*(lower4) + (480098681/100000000000000 : ℝ)*(upper5) + (58940094604017/5000000000000 : ℝ)*(major0) + (58940094604017/5000000000000 : ℝ)*(major1) + (58940094604017/5000000000000 : ℝ)*(major2) + (1048346993/10000000000000 : ℝ)*(sp4) + (127613660127/100000000000000 : ℝ)*(sp5) + (97278971413/50000000000000 : ℝ)*(sp6) + (55211447043/100000000000000 : ℝ)*(sp7) + (1833205625843653/100000000000000 : ℝ)*(sp12) + (114568030978341/6250000000000 : ℝ)*(sp13) + (916510775685379/50000000000000 : ℝ)*(sp14) + (1110558714879/200000000000 : ℝ)*(sp15) + (277667284443271/50000000000000 : ℝ)*(f.failure) + (1833216109313583/100000000000000 : ℝ)*(f.sum) + (153412553541/376375000000000000000000000 : ℝ)*base65 + (361985121270981759/37637500000000000000000000000000 : ℝ)*base68 + (190319877977843241/37637500000000000000000000000000 : ℝ)*base69 + (48840590752843241/37637500000000000000000000000000 : ℝ)*base71 + (13811260238753/1505500000000000000000000000 : ℝ)*base74 + (120824287822694259/37637500000000000000000000000000 : ℝ)*base76 + (306758995410744259/37637500000000000000000000000000 : ℝ)*base78 + (373191416319994259/37637500000000000000000000000000 : ℝ)*base80 + (6472563251663/3011000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2924213/625000000000000000000 : ℝ)*base90 + (2924213/625000000000000000000 : ℝ)*base92 + (2924213/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1747_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26533597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68857/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57963/100000 : ℝ) else (8139/10000 : ℝ) ≤ X j i ∧ X j i ≤ (92843/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1747_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1747_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26533597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3607/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/100 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68857/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57963/100000 : ℝ) else (8139/10000 : ℝ) ≤ X j i ∧ X j i ≤ (92843/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1747_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1747_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5711/1024 : ℝ) ≤ p) (hpb : p ≤ (5727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (26533597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3607/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9/100 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68857/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57963/100000 : ℝ) else (8139/10000 : ℝ) ≤ X j i ∧ X j i ≤ (92843/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1747_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

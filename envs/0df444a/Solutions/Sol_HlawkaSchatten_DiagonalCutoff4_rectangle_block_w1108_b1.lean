-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1108_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:04:06.679281+00:00
-- url     : https://prove2.me/submissions/43d0a588-bc8f-4f8d-8c24-91cb527f8c51

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
theorem support_rectangle_w1108_s3_0 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-87162329/400000000 : ℝ)*x 0 + (5432789113/10000000000 : ℝ)*x 1 + (104575431/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87162329/400000000 : ℝ)^8301 ≤ (6614648979721/50000000000000 : ℝ)^6253 := by
    have hnat : (87162329 : ℕ)^8301*50000000000000^6253 ≤ 6614648979721^6253*400000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87162329 400000000 6614648979721 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432789113/10000000000 : ℝ)^8301 ≤ (44487376053327/100000000000000 : ℝ)^6253 := by
    have hnat : (5432789113 : ℕ)^8301*100000000000000^6253 ≤ 44487376053327^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432789113 10000000000 44487376053327 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104575431/200000000 : ℝ)^8301 ≤ (21141662984867/50000000000000 : ℝ)^6253 := by
    have hnat : (104575431 : ℕ)^8301*50000000000000^6253 ≤ 21141662984867^6253*200000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104575431 200000000 21141662984867 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87162329/400000000 : ℝ), (5432789113/10000000000 : ℝ), (104575431/200000000 : ℝ)] ![(6614648979721/50000000000000 : ℝ), (44487376053327/100000000000000 : ℝ), (21141662984867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87162329/400000000 : ℝ)|^8301 ≤ (6614648979721/50000000000000 : ℝ)^6253
        have hw : |(-87162329/400000000 : ℝ)|=(87162329/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432789113/10000000000 : ℝ)|^8301 ≤ (44487376053327/100000000000000 : ℝ)^6253
        have hw : |(5432789113/10000000000 : ℝ)|=(5432789113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104575431/200000000 : ℝ)|^8301 ≤ (21141662984867/50000000000000 : ℝ)^6253
        have hw : |(104575431/200000000 : ℝ)|=(104575431/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s3_1 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (669328227/1250000000 : ℝ)*x 0 + (-2283425207/10000000000 : ℝ)*x 1 + (2614385817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669328227/1250000000 : ℝ)^8301 ≤ (43639697827199/100000000000000 : ℝ)^6253 := by
    have hnat : (669328227 : ℕ)^8301*100000000000000^6253 ≤ 43639697827199^6253*1250000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669328227 1250000000 43639697827199 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2283425207/10000000000 : ℝ)^8301 ≤ (7038487637517/50000000000000 : ℝ)^6253 := by
    have hnat : (2283425207 : ℕ)^8301*50000000000000^6253 ≤ 7038487637517^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283425207 10000000000 7038487637517 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614385817/5000000000 : ℝ)^8301 ≤ (21141663435747/50000000000000 : ℝ)^6253 := by
    have hnat : (2614385817 : ℕ)^8301*50000000000000^6253 ≤ 21141663435747^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614385817 5000000000 21141663435747 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669328227/1250000000 : ℝ), (-2283425207/10000000000 : ℝ), (2614385817/5000000000 : ℝ)] ![(43639697827199/100000000000000 : ℝ), (7038487637517/50000000000000 : ℝ), (21141663435747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669328227/1250000000 : ℝ)|^8301 ≤ (43639697827199/100000000000000 : ℝ)^6253
        have hw : |(669328227/1250000000 : ℝ)|=(669328227/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2283425207/10000000000 : ℝ)|^8301 ≤ (7038487637517/50000000000000 : ℝ)^6253
        have hw : |(-2283425207/10000000000 : ℝ)|=(2283425207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614385817/5000000000 : ℝ)|^8301 ≤ (21141663435747/50000000000000 : ℝ)^6253
        have hw : |(2614385817/5000000000 : ℝ)|=(2614385817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s3_2 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5354625949/10000000000 : ℝ)*x 0 + (5228771733/10000000000 : ℝ)*x 1 + (-2283424903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354625949/10000000000 : ℝ)^8301 ≤ (872793985323/2000000000000 : ℝ)^6253 := by
    have hnat : (5354625949 : ℕ)^8301*2000000000000^6253 ≤ 872793985323^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354625949 10000000000 872793985323 2000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228771733/10000000000 : ℝ)^8301 ≤ (21141663967141/50000000000000 : ℝ)^6253 := by
    have hnat : (5228771733 : ℕ)^8301*50000000000000^6253 ≤ 21141663967141^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228771733 10000000000 21141663967141 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2283424903/10000000000 : ℝ)^8301 ≤ (439905399597/3125000000000 : ℝ)^6253 := by
    have hnat : (2283424903 : ℕ)^8301*3125000000000^6253 ≤ 439905399597^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283424903 10000000000 439905399597 3125000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354625949/10000000000 : ℝ), (5228771733/10000000000 : ℝ), (-2283424903/10000000000 : ℝ)] ![(872793985323/2000000000000 : ℝ), (21141663967141/50000000000000 : ℝ), (439905399597/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354625949/10000000000 : ℝ)|^8301 ≤ (872793985323/2000000000000 : ℝ)^6253
        have hw : |(5354625949/10000000000 : ℝ)|=(5354625949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228771733/10000000000 : ℝ)|^8301 ≤ (21141663967141/50000000000000 : ℝ)^6253
        have hw : |(5228771733/10000000000 : ℝ)|=(5228771733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2283424903/10000000000 : ℝ)|^8301 ≤ (439905399597/3125000000000 : ℝ)^6253
        have hw : |(-2283424903/10000000000 : ℝ)|=(2283424903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s3_3 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366998523/10000000000 : ℝ)*x 0 + (4170067867/10000000000 : ℝ)*x 1 + (4573249567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366998523/10000000000 : ℝ)^8301 ≤ (6658321908259/20000000000000 : ℝ)^6253 := by
    have hnat : (4366998523 : ℕ)^8301*20000000000000^6253 ≤ 6658321908259^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366998523 10000000000 6658321908259 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170067867/10000000000 : ℝ)^8301 ≤ (31313480290187/100000000000000 : ℝ)^6253 := by
    have hnat : (4170067867 : ℕ)^8301*100000000000000^6253 ≤ 31313480290187^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170067867 10000000000 31313480290187 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4573249567/10000000000 : ℝ)^8301 ≤ (8848727536431/25000000000000 : ℝ)^6253 := by
    have hnat : (4573249567 : ℕ)^8301*25000000000000^6253 ≤ 8848727536431^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4573249567 10000000000 8848727536431 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366998523/10000000000 : ℝ), (4170067867/10000000000 : ℝ), (4573249567/10000000000 : ℝ)] ![(6658321908259/20000000000000 : ℝ), (31313480290187/100000000000000 : ℝ), (8848727536431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366998523/10000000000 : ℝ)|^8301 ≤ (6658321908259/20000000000000 : ℝ)^6253
        have hw : |(4366998523/10000000000 : ℝ)|=(4366998523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170067867/10000000000 : ℝ)|^8301 ≤ (31313480290187/100000000000000 : ℝ)^6253
        have hw : |(4170067867/10000000000 : ℝ)|=(4170067867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4573249567/10000000000 : ℝ)|^8301 ≤ (8848727536431/25000000000000 : ℝ)^6253
        have hw : |(4573249567/10000000000 : ℝ)|=(4573249567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s3_4 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-435815599/2000000000 : ℝ)*x 0 + (5229582707/10000000000 : ℝ)*x 1 + (1357993341/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435815599/2000000000 : ℝ)^8301 ≤ (413420540521/3125000000000 : ℝ)^6253 := by
    have hnat : (435815599 : ℕ)^8301*3125000000000^6253 ≤ 413420540521^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435815599 2000000000 413420540521 3125000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229582707/10000000000 : ℝ)^8301 ≤ (5286504268753/12500000000000 : ℝ)^6253 := by
    have hnat : (5229582707 : ℕ)^8301*12500000000000^6253 ≤ 5286504268753^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229582707 10000000000 5286504268753 12500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357993341/2500000000 : ℝ)^8301 ≤ (1779140341641/4000000000000 : ℝ)^6253 := by
    have hnat : (1357993341 : ℕ)^8301*4000000000000^6253 ≤ 1779140341641^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357993341 2500000000 1779140341641 4000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435815599/2000000000 : ℝ), (5229582707/10000000000 : ℝ), (1357993341/2500000000 : ℝ)] ![(413420540521/3125000000000 : ℝ), (5286504268753/12500000000000 : ℝ), (1779140341641/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435815599/2000000000 : ℝ)|^8301 ≤ (413420540521/3125000000000 : ℝ)^6253
        have hw : |(-435815599/2000000000 : ℝ)|=(435815599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229582707/10000000000 : ℝ)|^8301 ≤ (5286504268753/12500000000000 : ℝ)^6253
        have hw : |(5229582707/10000000000 : ℝ)|=(5229582707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357993341/2500000000 : ℝ)|^8301 ≤ (1779140341641/4000000000000 : ℝ)^6253
        have hw : |(1357993341/2500000000 : ℝ)|=(1357993341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s3_5 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5303069031/10000000000 : ℝ)*x 0 + (-416044663/2000000000 : ℝ)*x 1 + (1357993389/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303069031/10000000000 : ℝ)^8301 ≤ (43082776805787/100000000000000 : ℝ)^6253 := by
    have hnat : (5303069031 : ℕ)^8301*100000000000000^6253 ≤ 43082776805787^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303069031 10000000000 43082776805787 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416044663/2000000000 : ℝ)^8301 ≤ (6219356275809/50000000000000 : ℝ)^6253 := by
    have hnat : (416044663 : ℕ)^8301*50000000000000^6253 ≤ 6219356275809^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416044663 2000000000 6219356275809 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357993389/2500000000 : ℝ)^8301 ≤ (4447851062809/10000000000000 : ℝ)^6253 := by
    have hnat : (1357993389 : ℕ)^8301*10000000000000^6253 ≤ 4447851062809^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357993389 2500000000 4447851062809 10000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303069031/10000000000 : ℝ), (-416044663/2000000000 : ℝ), (1357993389/2500000000 : ℝ)] ![(43082776805787/100000000000000 : ℝ), (6219356275809/50000000000000 : ℝ), (4447851062809/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303069031/10000000000 : ℝ)|^8301 ≤ (43082776805787/100000000000000 : ℝ)^6253
        have hw : |(5303069031/10000000000 : ℝ)|=(5303069031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-416044663/2000000000 : ℝ)|^8301 ≤ (6219356275809/50000000000000 : ℝ)^6253
        have hw : |(-416044663/2000000000 : ℝ)|=(416044663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357993389/2500000000 : ℝ)|^8301 ≤ (4447851062809/10000000000000 : ℝ)^6253
        have hw : |(1357993389/2500000000 : ℝ)|=(1357993389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s3_6 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2651534543/5000000000 : ℝ)*x 0 + (5431973379/10000000000 : ℝ)*x 1 + (-2080223483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651534543/5000000000 : ℝ)^8301 ≤ (538534717487/1250000000000 : ℝ)^6253 := by
    have hnat : (2651534543 : ℕ)^8301*1250000000000^6253 ≤ 538534717487^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651534543 5000000000 538534717487 1250000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431973379/10000000000 : ℝ)^8301 ≤ (44478508704077/100000000000000 : ℝ)^6253 := by
    have hnat : (5431973379 : ℕ)^8301*100000000000000^6253 ≤ 44478508704077^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431973379 10000000000 44478508704077 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080223483/10000000000 : ℝ)^8301 ≤ (12438713885191/100000000000000 : ℝ)^6253 := by
    have hnat : (2080223483 : ℕ)^8301*100000000000000^6253 ≤ 12438713885191^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080223483 10000000000 12438713885191 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651534543/5000000000 : ℝ), (5431973379/10000000000 : ℝ), (-2080223483/10000000000 : ℝ)] ![(538534717487/1250000000000 : ℝ), (44478508704077/100000000000000 : ℝ), (12438713885191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651534543/5000000000 : ℝ)|^8301 ≤ (538534717487/1250000000000 : ℝ)^6253
        have hw : |(2651534543/5000000000 : ℝ)|=(2651534543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431973379/10000000000 : ℝ)|^8301 ≤ (44478508704077/100000000000000 : ℝ)^6253
        have hw : |(5431973379/10000000000 : ℝ)|=(5431973379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2080223483/10000000000 : ℝ)|^8301 ≤ (12438713885191/100000000000000 : ℝ)^6253
        have hw : |(-2080223483/10000000000 : ℝ)|=(2080223483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s3_7 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (109175939/250000000 : ℝ)*x 0 + (4571647373/10000000000 : ℝ)*x 1 + (1042919851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109175939/250000000 : ℝ)^8301 ≤ (33292004608339/100000000000000 : ℝ)^6253 := by
    have hnat : (109175939 : ℕ)^8301*100000000000000^6253 ≤ 33292004608339^6253*250000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109175939 250000000 33292004608339 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4571647373/10000000000 : ℝ)^8301 ≤ (35378449454083/100000000000000 : ℝ)^6253 := by
    have hnat : (4571647373 : ℕ)^8301*100000000000000^6253 ≤ 35378449454083^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4571647373 10000000000 35378449454083 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042919851/2500000000 : ℝ)^8301 ≤ (31329545927711/100000000000000 : ℝ)^6253 := by
    have hnat : (1042919851 : ℕ)^8301*100000000000000^6253 ≤ 31329545927711^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042919851 2500000000 31329545927711 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109175939/250000000 : ℝ), (4571647373/10000000000 : ℝ), (1042919851/2500000000 : ℝ)] ![(33292004608339/100000000000000 : ℝ), (35378449454083/100000000000000 : ℝ), (31329545927711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109175939/250000000 : ℝ)|^8301 ≤ (33292004608339/100000000000000 : ℝ)^6253
        have hw : |(109175939/250000000 : ℝ)|=(109175939/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4571647373/10000000000 : ℝ)|^8301 ≤ (35378449454083/100000000000000 : ℝ)^6253
        have hw : |(4571647373/10000000000 : ℝ)|=(4571647373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042919851/2500000000 : ℝ)|^8301 ≤ (31329545927711/100000000000000 : ℝ)^6253
        have hw : |(1042919851/2500000000 : ℝ)|=(1042919851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1108_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8303/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10531/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (464/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8303/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8913/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8303/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8913/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8303/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8913/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8303/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8913/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8303/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8913/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8303/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8913/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8913/100000 : ℝ) ^ (2075/512 : ℝ) ≤ (1111106757039141/20000000000000000000 : ℝ) := by
    have hpowers : (8913/100000 : ℝ)^2075 ≤ (1111106757039141/20000000000000000000 : ℝ)^512 := by
      have hnat : (8913 : ℕ)^2075*20000000000000000000^512 ≤ 1111106757039141^512*100000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8913 100000 1111106757039141 20000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8913/100000 : ℝ)) (X := (1111106757039141/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hpowhi : (8303/50000 : ℝ) ^ (2075/512 : ℝ) ≤ (17293436633420347/25000000000000000000 : ℝ) := by
    have hpowers : (8303/50000 : ℝ)^2075 ≤ (17293436633420347/25000000000000000000 : ℝ)^512 := by
      have hnat : (8303 : ℕ)^2075*25000000000000000000^512 ≤ 17293436633420347^512*50000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8303 50000 17293436633420347 25000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8303/50000 : ℝ)) (X := (17293436633420347/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001111106757039141/10000000000000000000 : ℝ) ≤ (312508567211669/312500000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (10001111106757039141/10000000000000000000 : ℝ)^512 ≤ (312508567211669/312500000000000 : ℝ)^2075 := by
      have hnat : (10001111106757039141 : ℕ)^512*312500000000000^2075 ≤ 312508567211669^2075*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001111106757039141 10000000000000000000 312508567211669 312500000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312508567211669/312500000000000 : ℝ)) (X := (10001111106757039141/10000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100074729280318877093/100000000000000000000 : ℝ) ≤ (1000184340373709/1000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (100074729280318877093/100000000000000000000 : ℝ)^512 ≤ (1000184340373709/1000000000000000 : ℝ)^2075 := by
      have hnat : (100074729280318877093 : ℕ)^512*1000000000000000^2075 ≤ 1000184340373709^2075*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100074729280318877093 100000000000000000000 1000184340373709 1000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000184340373709/1000000000000000 : ℝ)) (X := (100074729280318877093/100000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12517293436633420347/12500000000000000000 : ℝ) ≤ (2500853164175193/2500000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (12517293436633420347/12500000000000000000 : ℝ)^512 ≤ (2500853164175193/2500000000000000 : ℝ)^2075 := by
      have hnat : (12517293436633420347 : ℕ)^512*2500000000000000^2075 ≤ 2500853164175193^2075*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12517293436633420347 12500000000000000000 2500853164175193 2500000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500853164175193/2500000000000000 : ℝ)) (X := (12517293436633420347/12500000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1111106757039141/20000000000000000000 : ℝ) ≤ ((19226033884642308103/19232500000000000000 : ℝ)+2*(784626481841/384650000000000 : ℝ)*(8913/100000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (19226033884642308103/19232500000000000000 : ℝ)+2*(784626481841/384650000000000 : ℝ)*(8913/100000 : ℝ)=(312508567211669/312500000000000 : ℝ) by norm_num, show 1+2*(1111106757039141/20000000000000000000 : ℝ)=(10001111106757039141/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17293436633420347/25000000000000000000 : ℝ)+(1111106757039141/20000000000000000000 : ℝ) ≤ ((19226033884642308103/19232500000000000000 : ℝ)+(784626481841/384650000000000 : ℝ)*((8303/50000 : ℝ)+(8913/100000 : ℝ)))^(2075/512 : ℝ) := by
    rw [show (19226033884642308103/19232500000000000000 : ℝ)+(784626481841/384650000000000 : ℝ)*((8303/50000 : ℝ)+(8913/100000 : ℝ))=(1000184340373709/1000000000000000 : ℝ) by norm_num, show 1+(17293436633420347/25000000000000000000 : ℝ)+(1111106757039141/20000000000000000000 : ℝ)=(100074729280318877093/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17293436633420347/25000000000000000000 : ℝ) ≤ ((19226033884642308103/19232500000000000000 : ℝ)+2*(784626481841/384650000000000 : ℝ)*(8303/50000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (19226033884642308103/19232500000000000000 : ℝ)+2*(784626481841/384650000000000 : ℝ)*(8303/50000 : ℝ)=(2500853164175193/2500000000000000 : ℝ) by norm_num, show 1+2*(17293436633420347/25000000000000000000 : ℝ)=(12517293436633420347/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19226033884642308103/19232500000000000000 : ℝ)*(X 1 0+X 2 0)+(784626481841/384650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (8913/100000 : ℝ)) (hi := (8303/50000 : ℝ)) (c := (19226033884642308103/19232500000000000000 : ℝ)) (alpha := (784626481841/384650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19226033884642308103/19232500000000000000 : ℝ)*(X 0 1+X 2 1)+(784626481841/384650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (8913/100000 : ℝ)) (hi := (8303/50000 : ℝ)) (c := (19226033884642308103/19232500000000000000 : ℝ)) (alpha := (784626481841/384650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19226033884642308103/19232500000000000000 : ℝ)*(X 0 2+X 1 2)+(784626481841/384650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (8913/100000 : ℝ)) (hi := (8303/50000 : ℝ)) (c := (19226033884642308103/19232500000000000000 : ℝ)) (alpha := (784626481841/384650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-87162329/400000000 : ℝ)*X 0 0+(5432789113/10000000000 : ℝ)*X 0 1+(104575431/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669328227/1250000000 : ℝ)*X 1 0+(-2283425207/10000000000 : ℝ)*X 1 1+(2614385817/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354625949/10000000000 : ℝ)*X 2 0+(5228771733/10000000000 : ℝ)*X 2 1+(-2283424903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366998523/10000000000 : ℝ)*X 0 0+(4170067867/10000000000 : ℝ)*X 0 1+(4573249567/10000000000 : ℝ)*X 0 2+(4366998523/10000000000 : ℝ)*X 1 0+(4170067867/10000000000 : ℝ)*X 1 1+(4573249567/10000000000 : ℝ)*X 1 2+(4366998523/10000000000 : ℝ)*X 2 0+(4170067867/10000000000 : ℝ)*X 2 1+(4573249567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-435815599/2000000000 : ℝ)*X 0 0+(5229582707/10000000000 : ℝ)*X 0 1+(1357993341/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303069031/10000000000 : ℝ)*X 1 0+(-416044663/2000000000 : ℝ)*X 1 1+(1357993389/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651534543/5000000000 : ℝ)*X 2 0+(5431973379/10000000000 : ℝ)*X 2 1+(-2080223483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((109175939/250000000 : ℝ)*X 0 0+(4571647373/10000000000 : ℝ)*X 0 1+(1042919851/2500000000 : ℝ)*X 0 2+(109175939/250000000 : ℝ)*X 1 0+(4571647373/10000000000 : ℝ)*X 1 1+(1042919851/2500000000 : ℝ)*X 1 2+(109175939/250000000 : ℝ)*X 2 0+(4571647373/10000000000 : ℝ)*X 2 1+(1042919851/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (938100625448568462162603549/120203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2077533337/100000000000000 : ℝ)*(base19) + (390138761/20000000000000 : ℝ)*(base23) + (133109349/100000000000000 : ℝ)*(lower2) + (7631763/6250000000000 : ℝ)*(upper3) + (132952779/50000000000000 : ℝ)*(upper5) + (115342621358941/3125000000000 : ℝ)*(major0) + (115342621358941/3125000000000 : ℝ)*(major1) + (115342621358941/3125000000000 : ℝ)*(major2) + (1225393900043963/25000000000000 : ℝ)*(sp0) + (612702290083491/12500000000000 : ℝ)*(sp1) + (245080922375373/5000000000000 : ℝ)*(sp2) + (1240144714698379/50000000000000 : ℝ)*(sp3) + (44798025413/100000000000000 : ℝ)*(sp4) + (17679231033/100000000000000 : ℝ)*(sp7) + (155019194289237/6250000000000 : ℝ)*(f.failure) + (980324079640253/20000000000000 : ℝ)*(f.sum) + (246383966782649/38465000000000000000000000000 : ℝ)*base65 + (7516335352052101/30050781250000000000000000000000 : ℝ)*base68 + (26028621883947899/30050781250000000000000000000000 : ℝ)*base69 + (68753046303416649/30050781250000000000000000000000 : ℝ)*base71 + (277035874436849/38465000000000000000000000000 : ℝ)*base73 + (92434853279747387/15025390625000000000000000000000 : ℝ)*base75 + (23412733377597003/3756347656250000000000000000000 : ℝ)*base77 + (505131640763036529/120203125000000000000000000000000 : ℝ)*base80 + (25795529258893/19232500000000000000000000000 : ℝ)*base82 + (12079357/625000000000000000000 : ℝ)*base89 + (12079357/625000000000000000000 : ℝ)*base91 + (12079357/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1289531457784105429258061799/240406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119983507/12500000000000 : ℝ)*(base19) + (246831003/20000000000000 : ℝ)*(base23) + (151490163/100000000000000 : ℝ)*(upper3) + (107822611/100000000000000 : ℝ)*(lower4) + (3460689/6250000000000 : ℝ)*(upper5) + (930142008955713/25000000000000 : ℝ)*(major0) + (930142008955713/25000000000000 : ℝ)*(major1) + (930142008955713/25000000000000 : ℝ)*(major2) + (9395729401/50000000000000 : ℝ)*(sp1) + (20819971497/100000000000000 : ℝ)*(sp2) + (988186991848869/20000000000000 : ℝ)*(sp4) + (308807200494843/6250000000000 : ℝ)*(sp5) + (4940912905117833/100000000000000 : ℝ)*(sp6) + (250020093360241/10000000000000 : ℝ)*(sp7) + (250020093360241/10000000000000 : ℝ)*(f.failure) + (988186991848869/20000000000000 : ℝ)*(f.sum) + (74259094744939/38465000000000000000000000000 : ℝ)*base65 + (4595919347248129939/480812500000000000000000000000000 : ℝ)*base67 + (6117893151505942439/480812500000000000000000000000000 : ℝ)*base69 + (3702783532354692439/480812500000000000000000000000000 : ℝ)*base71 + (6644060972019/9616250000000000000000000000 : ℝ)*base74 + (3994844778962942439/480812500000000000000000000000000 : ℝ)*base75 + (4404558354193254939/480812500000000000000000000000000 : ℝ)*base77 + (4262273892532567439/480812500000000000000000000000000 : ℝ)*base79 + (72000853960543/19232500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9646599/1000000000000000000000 : ℝ)*base90 + (9646599/1000000000000000000000 : ℝ)*base92 + (9646599/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1108_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8303/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10531/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (464/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1108_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1108_s4_0 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1091172749/5000000000 : ℝ)*x 0 + (337723589/625000000 : ℝ)*x 1 + (656979277/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091172749/5000000000 : ℝ)^8301 ≤ (6627899195987/50000000000000 : ℝ)^6253 := by
    have hnat : (1091172749 : ℕ)^8301*50000000000000^6253 ≤ 6627899195987^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091172749 5000000000 6627899195987 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337723589/625000000 : ℝ)^8301 ≤ (22085052826653/50000000000000 : ℝ)^6253 := by
    have hnat : (337723589 : ℕ)^8301*50000000000000^6253 ≤ 22085052826653^6253*625000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337723589 625000000 22085052826653 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656979277/1250000000 : ℝ)^8301 ≤ (8514819188477/20000000000000 : ℝ)^6253 := by
    have hnat : (656979277 : ℕ)^8301*20000000000000^6253 ≤ 8514819188477^6253*1250000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656979277 1250000000 8514819188477 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1091172749/5000000000 : ℝ), (337723589/625000000 : ℝ), (656979277/1250000000 : ℝ)] ![(6627899195987/50000000000000 : ℝ), (22085052826653/50000000000000 : ℝ), (8514819188477/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1091172749/5000000000 : ℝ)|^8301 ≤ (6627899195987/50000000000000 : ℝ)^6253
        have hw : |(-1091172749/5000000000 : ℝ)|=(1091172749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337723589/625000000 : ℝ)|^8301 ≤ (22085052826653/50000000000000 : ℝ)^6253
        have hw : |(337723589/625000000 : ℝ)|=(337723589/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656979277/1250000000 : ℝ)|^8301 ≤ (8514819188477/20000000000000 : ℝ)^6253
        have hw : |(656979277/1250000000 : ℝ)|=(656979277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s4_1 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347356517/10000000000 : ℝ)*x 0 + (-2257455447/10000000000 : ℝ)*x 1 + (262791713/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347356517/10000000000 : ℝ)^8301 ≤ (8712213483689/20000000000000 : ℝ)^6253 := by
    have hnat : (5347356517 : ℕ)^8301*20000000000000^6253 ≤ 8712213483689^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347356517 10000000000 8712213483689 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257455447/10000000000 : ℝ)^8301 ≤ (13864836146067/100000000000000 : ℝ)^6253 := by
    have hnat : (2257455447 : ℕ)^8301*100000000000000^6253 ≤ 13864836146067^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257455447 10000000000 13864836146067 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262791713/500000000 : ℝ)^8301 ≤ (8514819283107/20000000000000 : ℝ)^6253 := by
    have hnat : (262791713 : ℕ)^8301*20000000000000^6253 ≤ 8514819283107^6253*500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262791713 500000000 8514819283107 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347356517/10000000000 : ℝ), (-2257455447/10000000000 : ℝ), (262791713/500000000 : ℝ)] ![(8712213483689/20000000000000 : ℝ), (13864836146067/100000000000000 : ℝ), (8514819283107/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347356517/10000000000 : ℝ)|^8301 ≤ (8712213483689/20000000000000 : ℝ)^6253
        have hw : |(5347356517/10000000000 : ℝ)|=(5347356517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2257455447/10000000000 : ℝ)|^8301 ≤ (13864836146067/100000000000000 : ℝ)^6253
        have hw : |(-2257455447/10000000000 : ℝ)|=(2257455447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262791713/500000000 : ℝ)|^8301 ≤ (8514819283107/20000000000000 : ℝ)^6253
        have hw : |(262791713/500000000 : ℝ)|=(262791713/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s4_2 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347356803/10000000000 : ℝ)*x 0 + (5255834071/10000000000 : ℝ)*x 1 + (-2257455317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347356803/10000000000 : ℝ)^8301 ≤ (8712214102271/20000000000000 : ℝ)^6253 := by
    have hnat : (5347356803 : ℕ)^8301*20000000000000^6253 ≤ 8712214102271^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347356803 10000000000 8712214102271 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255834071/10000000000 : ℝ)^8301 ≤ (21287047191571/50000000000000 : ℝ)^6253 := by
    have hnat : (5255834071 : ℕ)^8301*50000000000000^6253 ≤ 21287047191571^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255834071 10000000000 21287047191571 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257455317/10000000000 : ℝ)^8301 ≤ (866552192883/6250000000000 : ℝ)^6253 := by
    have hnat : (2257455317 : ℕ)^8301*6250000000000^6253 ≤ 866552192883^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257455317 10000000000 866552192883 6250000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347356803/10000000000 : ℝ), (5255834071/10000000000 : ℝ), (-2257455317/10000000000 : ℝ)] ![(8712214102271/20000000000000 : ℝ), (21287047191571/50000000000000 : ℝ), (866552192883/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347356803/10000000000 : ℝ)|^8301 ≤ (8712214102271/20000000000000 : ℝ)^6253
        have hw : |(5347356803/10000000000 : ℝ)|=(5347356803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255834071/10000000000 : ℝ)|^8301 ≤ (21287047191571/50000000000000 : ℝ)^6253
        have hw : |(5255834071/10000000000 : ℝ)|=(5255834071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2257455317/10000000000 : ℝ)|^8301 ≤ (866552192883/6250000000000 : ℝ)^6253
        have hw : |(-2257455317/10000000000 : ℝ)|=(2257455317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s4_3 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (87379163/200000000 : ℝ)*x 0 + (16901667/40000000 : ℝ)*x 1 + (2258694963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87379163/200000000 : ℝ)^8301 ≤ (16655721513719/50000000000000 : ℝ)^6253 := by
    have hnat : (87379163 : ℕ)^8301*50000000000000^6253 ≤ 16655721513719^6253*200000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87379163 200000000 16655721513719 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16901667/40000000 : ℝ)^8301 ≤ (31866421843343/100000000000000 : ℝ)^6253 := by
    have hnat : (16901667 : ℕ)^8301*100000000000000^6253 ≤ 31866421843343^6253*40000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16901667 40000000 31866421843343 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258694963/5000000000 : ℝ)^8301 ≤ (34822135119779/100000000000000 : ℝ)^6253 := by
    have hnat : (2258694963 : ℕ)^8301*100000000000000^6253 ≤ 34822135119779^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258694963 5000000000 34822135119779 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87379163/200000000 : ℝ), (16901667/40000000 : ℝ), (2258694963/5000000000 : ℝ)] ![(16655721513719/50000000000000 : ℝ), (31866421843343/100000000000000 : ℝ), (34822135119779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87379163/200000000 : ℝ)|^8301 ≤ (16655721513719/50000000000000 : ℝ)^6253
        have hw : |(87379163/200000000 : ℝ)|=(87379163/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16901667/40000000 : ℝ)|^8301 ≤ (31866421843343/100000000000000 : ℝ)^6253
        have hw : |(16901667/40000000 : ℝ)|=(16901667/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2258694963/5000000000 : ℝ)|^8301 ≤ (34822135119779/100000000000000 : ℝ)^6253
        have hw : |(2258694963/5000000000 : ℝ)|=(2258694963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s4_4 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2182353653/10000000000 : ℝ)*x 0 + (262812993/500000000 : ℝ)*x 1 + (1350787389/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182353653/10000000000 : ℝ)^8301 ≤ (530234565999/4000000000000 : ℝ)^6253 := by
    have hnat : (2182353653 : ℕ)^8301*4000000000000^6253 ≤ 530234565999^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182353653 10000000000 530234565999 4000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262812993/500000000 : ℝ)^8301 ≤ (21289336561433/50000000000000 : ℝ)^6253 := by
    have hnat : (262812993 : ℕ)^8301*50000000000000^6253 ≤ 21289336561433^6253*500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262812993 500000000 21289336561433 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350787389/2500000000 : ℝ)^8301 ≤ (8833092542343/20000000000000 : ℝ)^6253 := by
    have hnat : (1350787389 : ℕ)^8301*20000000000000^6253 ≤ 8833092542343^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350787389 2500000000 8833092542343 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2182353653/10000000000 : ℝ), (262812993/500000000 : ℝ), (1350787389/2500000000 : ℝ)] ![(530234565999/4000000000000 : ℝ), (21289336561433/50000000000000 : ℝ), (8833092542343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2182353653/10000000000 : ℝ)|^8301 ≤ (530234565999/4000000000000 : ℝ)^6253
        have hw : |(-2182353653/10000000000 : ℝ)|=(2182353653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262812993/500000000 : ℝ)|^8301 ≤ (21289336561433/50000000000000 : ℝ)^6253
        have hw : |(262812993/500000000 : ℝ)|=(262812993/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350787389/2500000000 : ℝ)|^8301 ≤ (8833092542343/20000000000000 : ℝ)^6253
        have hw : |(1350787389/2500000000 : ℝ)|=(1350787389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s4_5 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663752873/1250000000 : ℝ)*x 0 + (-422027951/2000000000 : ℝ)*x 1 + (5403149697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663752873/1250000000 : ℝ)^8301 ≤ (43157790985829/100000000000000 : ℝ)^6253 := by
    have hnat : (663752873 : ℕ)^8301*100000000000000^6253 ≤ 43157790985829^6253*1250000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663752873 1250000000 43157790985829 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422027951/2000000000 : ℝ)^8301 ≤ (1584593093837/12500000000000 : ℝ)^6253 := by
    have hnat : (422027951 : ℕ)^8301*12500000000000^6253 ≤ 1584593093837^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422027951 2000000000 1584593093837 12500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403149697/10000000000 : ℝ)^8301 ≤ (22082732120867/50000000000000 : ℝ)^6253 := by
    have hnat : (5403149697 : ℕ)^8301*50000000000000^6253 ≤ 22082732120867^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403149697 10000000000 22082732120867 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663752873/1250000000 : ℝ), (-422027951/2000000000 : ℝ), (5403149697/10000000000 : ℝ)] ![(43157790985829/100000000000000 : ℝ), (1584593093837/12500000000000 : ℝ), (22082732120867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663752873/1250000000 : ℝ)|^8301 ≤ (43157790985829/100000000000000 : ℝ)^6253
        have hw : |(663752873/1250000000 : ℝ)|=(663752873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422027951/2000000000 : ℝ)|^8301 ≤ (1584593093837/12500000000000 : ℝ)^6253
        have hw : |(-422027951/2000000000 : ℝ)|=(422027951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403149697/10000000000 : ℝ)|^8301 ≤ (22082732120867/50000000000000 : ℝ)^6253
        have hw : |(5403149697/10000000000 : ℝ)|=(5403149697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s4_6 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062004639/2000000000 : ℝ)*x 0 + (1080629917/2000000000 : ℝ)*x 1 + (-2110139623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062004639/2000000000 : ℝ)^8301 ≤ (43157793262431/100000000000000 : ℝ)^6253 := by
    have hnat : (1062004639 : ℕ)^8301*100000000000000^6253 ≤ 43157793262431^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062004639 2000000000 43157793262431 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080629917/2000000000 : ℝ)^8301 ≤ (55206828783/125000000000 : ℝ)^6253 := by
    have hnat : (1080629917 : ℕ)^8301*125000000000^6253 ≤ 55206828783^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080629917 2000000000 55206828783 125000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110139623/10000000000 : ℝ)^8301 ≤ (12676743697977/100000000000000 : ℝ)^6253 := by
    have hnat : (2110139623 : ℕ)^8301*100000000000000^6253 ≤ 12676743697977^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110139623 10000000000 12676743697977 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062004639/2000000000 : ℝ), (1080629917/2000000000 : ℝ), (-2110139623/10000000000 : ℝ)] ![(43157793262431/100000000000000 : ℝ), (55206828783/125000000000 : ℝ), (12676743697977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062004639/2000000000 : ℝ)|^8301 ≤ (43157793262431/100000000000000 : ℝ)^6253
        have hw : |(1062004639/2000000000 : ℝ)|=(1062004639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080629917/2000000000 : ℝ)|^8301 ≤ (55206828783/125000000000 : ℝ)^6253
        have hw : |(1080629917/2000000000 : ℝ)|=(1080629917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2110139623/10000000000 : ℝ)|^8301 ≤ (12676743697977/100000000000000 : ℝ)^6253
        have hw : |(-2110139623/10000000000 : ℝ)|=(2110139623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s4_7 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873794617/2000000000 : ℝ)*x 0 + (225827389/500000000 : ℝ)*x 1 + (33810099/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873794617/2000000000 : ℝ)^8301 ≤ (6662318839307/20000000000000 : ℝ)^6253 := by
    have hnat : (873794617 : ℕ)^8301*20000000000000^6253 ≤ 6662318839307^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873794617 2000000000 6662318839307 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225827389/500000000 : ℝ)^8301 ≤ (4351689695921/12500000000000 : ℝ)^6253 := by
    have hnat : (225827389 : ℕ)^8301*12500000000000^6253 ≤ 4351689695921^6253*500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225827389 500000000 4351689695921 12500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33810099/80000000 : ℝ)^8301 ≤ (7968722055961/25000000000000 : ℝ)^6253 := by
    have hnat : (33810099 : ℕ)^8301*25000000000000^6253 ≤ 7968722055961^6253*80000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33810099 80000000 7968722055961 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873794617/2000000000 : ℝ), (225827389/500000000 : ℝ), (33810099/80000000 : ℝ)] ![(6662318839307/20000000000000 : ℝ), (4351689695921/12500000000000 : ℝ), (7968722055961/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873794617/2000000000 : ℝ)|^8301 ≤ (6662318839307/20000000000000 : ℝ)^6253
        have hw : |(873794617/2000000000 : ℝ)|=(873794617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225827389/500000000 : ℝ)|^8301 ≤ (4351689695921/12500000000000 : ℝ)^6253
        have hw : |(225827389/500000000 : ℝ)|=(225827389/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33810099/80000000 : ℝ)|^8301 ≤ (7968722055961/25000000000000 : ℝ)^6253
        have hw : |(33810099/80000000 : ℝ)|=(33810099/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1108_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (464/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10531/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11109/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (464/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10531/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (464/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10531/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (464/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10531/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (464/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10531/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (464/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10531/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (464/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10531/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10531/100000 : ℝ) ^ (2075/512 : ℝ) ≤ (10922674634729701/100000000000000000000 : ℝ) := by
    have hpowers : (10531/100000 : ℝ)^2075 ≤ (10922674634729701/100000000000000000000 : ℝ)^512 := by
      have hnat : (10531 : ℕ)^2075*100000000000000000000^512 ≤ 10922674634729701^512*100000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10531 100000 10922674634729701 100000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10531/100000 : ℝ)) (X := (10922674634729701/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hpowhi : (464/3125 : ℝ) ^ (2075/512 : ℝ) ≤ (2747073505776817/6250000000000000000 : ℝ) := by
    have hpowers : (464/3125 : ℝ)^2075 ≤ (2747073505776817/6250000000000000000 : ℝ)^512 := by
      have hnat : (464 : ℕ)^2075*6250000000000000000^512 ≤ 2747073505776817^512*3125^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        464 3125 2747073505776817 6250000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (464/3125 : ℝ)) (X := (2747073505776817/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010922674634729701/50000000000000000000 : ℝ) ≤ (5000269491535139/5000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (50010922674634729701/50000000000000000000 : ℝ)^512 ≤ (5000269491535139/5000000000000000 : ℝ)^2075 := by
      have hnat : (50010922674634729701 : ℕ)^512*5000000000000000^2075 ≤ 5000269491535139^2075*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010922674634729701 50000000000000000000 5000269491535139 5000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000269491535139/5000000000000000 : ℝ)) (X := (50010922674634729701/50000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100054875850727158773/100000000000000000000 : ℝ) ≤ (5000676882663781/5000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (100054875850727158773/100000000000000000000 : ℝ)^512 ≤ (5000676882663781/5000000000000000 : ℝ)^2075 := by
      have hnat : (100054875850727158773 : ℕ)^512*5000000000000000^2075 ≤ 5000676882663781^2075*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100054875850727158773 100000000000000000000 5000676882663781 5000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000676882663781/5000000000000000 : ℝ)) (X := (100054875850727158773/100000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127747073505776817/3125000000000000000 : ℝ) ≤ (5001084273792423/5000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (3127747073505776817/3125000000000000000 : ℝ)^512 ≤ (5001084273792423/5000000000000000 : ℝ)^2075 := by
      have hnat : (3127747073505776817 : ℕ)^512*5000000000000000^2075 ≤ 5001084273792423^2075*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127747073505776817 3125000000000000000 5001084273792423 5000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001084273792423/5000000000000000 : ℝ)) (X := (3127747073505776817/3125000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10922674634729701/100000000000000000000 : ℝ) ≤ ((21577582923005737259/21585000000000000000 : ℝ)+2*(203695564321/107925000000000 : ℝ)*(10531/100000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (21577582923005737259/21585000000000000000 : ℝ)+2*(203695564321/107925000000000 : ℝ)*(10531/100000 : ℝ)=(5000269491535139/5000000000000000 : ℝ) by norm_num, show 1+2*(10922674634729701/100000000000000000000 : ℝ)=(50010922674634729701/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2747073505776817/6250000000000000000 : ℝ)+(10922674634729701/100000000000000000000 : ℝ) ≤ ((21577582923005737259/21585000000000000000 : ℝ)+(203695564321/107925000000000 : ℝ)*((464/3125 : ℝ)+(10531/100000 : ℝ)))^(2075/512 : ℝ) := by
    rw [show (21577582923005737259/21585000000000000000 : ℝ)+(203695564321/107925000000000 : ℝ)*((464/3125 : ℝ)+(10531/100000 : ℝ))=(5000676882663781/5000000000000000 : ℝ) by norm_num, show 1+(2747073505776817/6250000000000000000 : ℝ)+(10922674634729701/100000000000000000000 : ℝ)=(100054875850727158773/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2747073505776817/6250000000000000000 : ℝ) ≤ ((21577582923005737259/21585000000000000000 : ℝ)+2*(203695564321/107925000000000 : ℝ)*(464/3125 : ℝ))^(2075/512 : ℝ) := by
    rw [show (21577582923005737259/21585000000000000000 : ℝ)+2*(203695564321/107925000000000 : ℝ)*(464/3125 : ℝ)=(5001084273792423/5000000000000000 : ℝ) by norm_num, show 1+2*(2747073505776817/6250000000000000000 : ℝ)=(3127747073505776817/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21577582923005737259/21585000000000000000 : ℝ)*(X 1 0+X 2 0)+(203695564321/107925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (10531/100000 : ℝ)) (hi := (464/3125 : ℝ)) (c := (21577582923005737259/21585000000000000000 : ℝ)) (alpha := (203695564321/107925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21577582923005737259/21585000000000000000 : ℝ)*(X 0 1+X 2 1)+(203695564321/107925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (10531/100000 : ℝ)) (hi := (464/3125 : ℝ)) (c := (21577582923005737259/21585000000000000000 : ℝ)) (alpha := (203695564321/107925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21577582923005737259/21585000000000000000 : ℝ)*(X 0 2+X 1 2)+(203695564321/107925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (10531/100000 : ℝ)) (hi := (464/3125 : ℝ)) (c := (21577582923005737259/21585000000000000000 : ℝ)) (alpha := (203695564321/107925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1091172749/5000000000 : ℝ)*X 0 0+(337723589/625000000 : ℝ)*X 0 1+(656979277/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347356517/10000000000 : ℝ)*X 1 0+(-2257455447/10000000000 : ℝ)*X 1 1+(262791713/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347356803/10000000000 : ℝ)*X 2 0+(5255834071/10000000000 : ℝ)*X 2 1+(-2257455317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((87379163/200000000 : ℝ)*X 0 0+(16901667/40000000 : ℝ)*X 0 1+(2258694963/5000000000 : ℝ)*X 0 2+(87379163/200000000 : ℝ)*X 1 0+(16901667/40000000 : ℝ)*X 1 1+(2258694963/5000000000 : ℝ)*X 1 2+(87379163/200000000 : ℝ)*X 2 0+(16901667/40000000 : ℝ)*X 2 1+(2258694963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2182353653/10000000000 : ℝ)*X 0 0+(262812993/500000000 : ℝ)*X 0 1+(1350787389/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663752873/1250000000 : ℝ)*X 1 0+(-422027951/2000000000 : ℝ)*X 1 1+(5403149697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062004639/2000000000 : ℝ)*X 2 0+(1080629917/2000000000 : ℝ)*X 2 1+(-2110139623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873794617/2000000000 : ℝ)*X 0 0+(225827389/500000000 : ℝ)*X 0 1+(33810099/80000000 : ℝ)*X 0 2+(873794617/2000000000 : ℝ)*X 1 0+(225827389/500000000 : ℝ)*X 1 1+(33810099/80000000 : ℝ)*X 1 2+(873794617/2000000000 : ℝ)*X 2 0+(225827389/500000000 : ℝ)*X 2 1+(33810099/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1789418811914563749188571119/179875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (187930617/50000000000000 : ℝ)*(base19) + (156013171/100000000000000 : ℝ)*(base23) + (405696553/100000000000000 : ℝ)*(lower2) + (94593971/50000000000000 : ℝ)*(upper3) + (23639213/25000000000000 : ℝ)*(lower4) + (2548370541223847/50000000000000 : ℝ)*(major0) + (2548370541223847/50000000000000 : ℝ)*(major1) + (2548370541223847/50000000000000 : ℝ)*(major2) + (3384249508693099/50000000000000 : ℝ)*(sp0) + (3384249962523807/50000000000000 : ℝ)*(sp1) + (6768500144895677/100000000000000 : ℝ)*(sp2) + (85624323145781/2500000000000 : ℝ)*(sp3) + (25670453/2000000000000 : ℝ)*(sp4) + (172131023/2000000000000 : ℝ)*(sp7) + (342498153238239/10000000000000 : ℝ)*(f.failure) + (423031268806803/6250000000000 : ℝ)*(f.sum) + (10277237766871/1349062500000000000000000000 : ℝ)*base65 + (20724892828231384627/1079250000000000000000000000000000 : ℝ)*base68 + (18253975537931884627/1079250000000000000000000000000000 : ℝ)*base70 + (10329410304934384627/1079250000000000000000000000000000 : ℝ)*base72 + (1063300724513/10792500000000000000000000000 : ℝ)*base73 + (25802748081587884627/1079250000000000000000000000000000 : ℝ)*base76 + (14509388933229634627/1079250000000000000000000000000000 : ℝ)*base78 + (40496092451345134627/1079250000000000000000000000000000 : ℝ)*base80 + (102701843353289/21585000000000000000000000000 : ℝ)*base82 + (19889879/1000000000000000000000 : ℝ)*base89 + (19889879/1000000000000000000000 : ℝ)*base91 + (19889879/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (501941278020790136745481359/44968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (468891139/25000000000000 : ℝ)*(base19) + (2413961857/100000000000000 : ℝ)*(base23) + (36201523/12500000000000 : ℝ)*(upper3) + (52352853/50000000000000 : ℝ)*(lower4) + (184405703/50000000000000 : ℝ)*(upper5) + (1281589798711151/25000000000000 : ℝ)*(major0) + (1281589798711151/25000000000000 : ℝ)*(major1) + (1281589798711151/25000000000000 : ℝ)*(major2) + (2269101019/5000000000000 : ℝ)*(sp1) + (55437016241/100000000000000 : ℝ)*(sp2) + (3403916639591509/50000000000000 : ℝ)*(sp4) + (3403893010799041/50000000000000 : ℝ)*(sp5) + (170194385705123/2500000000000 : ℝ)*(sp6) + (68897694768789/2000000000000 : ℝ)*(sp7) + (68897694768789/2000000000000 : ℝ)*(f.failure) + (3403916639591509/50000000000000 : ℝ)*(f.sum) + (4244967541211/1349062500000000000000000000 : ℝ)*base65 + (2130280286836324891/539625000000000000000000000000000 : ℝ)*base68 + (10761126328727074891/539625000000000000000000000000000 : ℝ)*base70 + (1897179646662925109/539625000000000000000000000000000 : ℝ)*base71 + (27035026972993/10792500000000000000000000000 : ℝ)*base73 + (3037398127087324891/539625000000000000000000000000000 : ℝ)*base76 + (2039829257921449891/539625000000000000000000000000000 : ℝ)*base78 + (4134473347639699891/539625000000000000000000000000000 : ℝ)*base80 + (32882613895369/21585000000000000000000000000 : ℝ)*base82 + (2138429/200000000000000000000 : ℝ)*base89 + (2138429/200000000000000000000 : ℝ)*base91 + (2138429/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1108_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (464/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10531/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1108_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1108_s5_0 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183059303/10000000000 : ℝ)*x 0 + (5395825869/10000000000 : ℝ)*x 1 + (5263117703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183059303/10000000000 : ℝ)^8301 ≤ (663077723859/5000000000000 : ℝ)^6253 := by
    have hnat : (2183059303 : ℕ)^8301*5000000000000^6253 ≤ 663077723859^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183059303 10000000000 663077723859 5000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395825869/10000000000 : ℝ)^8301 ≤ (11021502390607/25000000000000 : ℝ)^6253 := by
    have hnat : (5395825869 : ℕ)^8301*25000000000000^6253 ≤ 11021502390607^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395825869 10000000000 11021502390607 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263117703/10000000000 : ℝ)^8301 ≤ (1066310898833/2500000000000 : ℝ)^6253 := by
    have hnat : (5263117703 : ℕ)^8301*2500000000000^6253 ≤ 1066310898833^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263117703 10000000000 1066310898833 2500000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183059303/10000000000 : ℝ), (5395825869/10000000000 : ℝ), (5263117703/10000000000 : ℝ)] ![(663077723859/5000000000000 : ℝ), (11021502390607/25000000000000 : ℝ), (1066310898833/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183059303/10000000000 : ℝ)|^8301 ≤ (663077723859/5000000000000 : ℝ)^6253
        have hw : |(-2183059303/10000000000 : ℝ)|=(2183059303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395825869/10000000000 : ℝ)|^8301 ≤ (11021502390607/25000000000000 : ℝ)^6253
        have hw : |(5395825869/10000000000 : ℝ)|=(5395825869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263117703/10000000000 : ℝ)|^8301 ≤ (1066310898833/2500000000000 : ℝ)^6253
        have hw : |(5263117703/10000000000 : ℝ)|=(5263117703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s5_1 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345420221/10000000000 : ℝ)*x 0 + (-2250412603/10000000000 : ℝ)*x 1 + (263155851/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345420221/10000000000 : ℝ)^8301 ≤ (21770064416211/50000000000000 : ℝ)^6253 := by
    have hnat : (5345420221 : ℕ)^8301*50000000000000^6253 ≤ 21770064416211^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345420221 10000000000 21770064416211 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250412603/10000000000 : ℝ)^8301 ≤ (13807442540057/100000000000000 : ℝ)^6253 := by
    have hnat : (2250412603 : ℕ)^8301*100000000000000^6253 ≤ 13807442540057^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250412603 10000000000 13807442540057 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263155851/500000000 : ℝ)^8301 ≤ (42652428605417/100000000000000 : ℝ)^6253 := by
    have hnat : (263155851 : ℕ)^8301*100000000000000^6253 ≤ 42652428605417^6253*500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263155851 500000000 42652428605417 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345420221/10000000000 : ℝ), (-2250412603/10000000000 : ℝ), (263155851/500000000 : ℝ)] ![(21770064416211/50000000000000 : ℝ), (13807442540057/100000000000000 : ℝ), (42652428605417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345420221/10000000000 : ℝ)|^8301 ≤ (21770064416211/50000000000000 : ℝ)^6253
        have hw : |(5345420221/10000000000 : ℝ)|=(5345420221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2250412603/10000000000 : ℝ)|^8301 ≤ (13807442540057/100000000000000 : ℝ)^6253
        have hw : |(-2250412603/10000000000 : ℝ)|=(2250412603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263155851/500000000 : ℝ)|^8301 ≤ (42652428605417/100000000000000 : ℝ)^6253
        have hw : |(263155851/500000000 : ℝ)|=(263155851/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s5_2 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345419387/10000000000 : ℝ)*x 0 + (5263117349/10000000000 : ℝ)*x 1 + (-2250413277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345419387/10000000000 : ℝ)^8301 ≤ (1360628744197/3125000000000 : ℝ)^6253 := by
    have hnat : (5345419387 : ℕ)^8301*3125000000000^6253 ≤ 1360628744197^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345419387 10000000000 1360628744197 3125000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263117349/10000000000 : ℝ)^8301 ≤ (4265243214489/10000000000000 : ℝ)^6253 := by
    have hnat : (5263117349 : ℕ)^8301*10000000000000^6253 ≤ 4265243214489^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263117349 10000000000 4265243214489 10000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250413277/10000000000 : ℝ)^8301 ≤ (3451862007453/25000000000000 : ℝ)^6253 := by
    have hnat : (2250413277 : ℕ)^8301*25000000000000^6253 ≤ 3451862007453^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250413277 10000000000 3451862007453 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345419387/10000000000 : ℝ), (5263117349/10000000000 : ℝ), (-2250413277/10000000000 : ℝ)] ![(1360628744197/3125000000000 : ℝ), (4265243214489/10000000000000 : ℝ), (3451862007453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345419387/10000000000 : ℝ)|^8301 ≤ (1360628744197/3125000000000 : ℝ)^6253
        have hw : |(5345419387/10000000000 : ℝ)|=(5345419387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263117349/10000000000 : ℝ)|^8301 ≤ (4265243214489/10000000000000 : ℝ)^6253
        have hw : |(5263117349/10000000000 : ℝ)|=(5263117349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2250413277/10000000000 : ℝ)|^8301 ≤ (3451862007453/25000000000000 : ℝ)^6253
        have hw : |(-2250413277/10000000000 : ℝ)|=(2250413277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s5_3 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369375321/10000000000 : ℝ)*x 0 + (848043659/2000000000 : ℝ)*x 1 + (180099191/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369375321/10000000000 : ℝ)^8301 ≤ (33315665612901/100000000000000 : ℝ)^6253 := by
    have hnat : (4369375321 : ℕ)^8301*100000000000000^6253 ≤ 33315665612901^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369375321 10000000000 33315665612901 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848043659/2000000000 : ℝ)^8301 ≤ (32014694699699/100000000000000 : ℝ)^6253 := by
    have hnat : (848043659 : ℕ)^8301*100000000000000^6253 ≤ 32014694699699^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848043659 2000000000 32014694699699 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180099191/400000000 : ℝ)^8301 ≤ (34669639677087/100000000000000 : ℝ)^6253 := by
    have hnat : (180099191 : ℕ)^8301*100000000000000^6253 ≤ 34669639677087^6253*400000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180099191 400000000 34669639677087 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369375321/10000000000 : ℝ), (848043659/2000000000 : ℝ), (180099191/400000000 : ℝ)] ![(33315665612901/100000000000000 : ℝ), (32014694699699/100000000000000 : ℝ), (34669639677087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369375321/10000000000 : ℝ)|^8301 ≤ (33315665612901/100000000000000 : ℝ)^6253
        have hw : |(4369375321/10000000000 : ℝ)|=(4369375321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(848043659/2000000000 : ℝ)|^8301 ≤ (32014694699699/100000000000000 : ℝ)^6253
        have hw : |(848043659/2000000000 : ℝ)|=(848043659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(180099191/400000000 : ℝ)|^8301 ≤ (34669639677087/100000000000000 : ℝ)^6253
        have hw : |(180099191/400000000 : ℝ)|=(180099191/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s5_4 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183064677/10000000000 : ℝ)*x 0 + (5263461517/10000000000 : ℝ)*x 1 + (1348870211/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183064677/10000000000 : ℝ)^8301 ≤ (6630798907583/50000000000000 : ℝ)^6253 := by
    have hnat : (2183064677 : ℕ)^8301*50000000000000^6253 ≤ 6630798907583^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183064677 10000000000 6630798907583 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263461517/10000000000 : ℝ)^8301 ≤ (42656134839307/100000000000000 : ℝ)^6253 := by
    have hnat : (5263461517 : ℕ)^8301*100000000000000^6253 ≤ 42656134839307^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263461517 10000000000 42656134839307 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348870211/2500000000 : ℝ)^8301 ≤ (44082267329063/100000000000000 : ℝ)^6253 := by
    have hnat : (1348870211 : ℕ)^8301*100000000000000^6253 ≤ 44082267329063^6253*2500000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348870211 2500000000 44082267329063 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183064677/10000000000 : ℝ), (5263461517/10000000000 : ℝ), (1348870211/2500000000 : ℝ)] ![(6630798907583/50000000000000 : ℝ), (42656134839307/100000000000000 : ℝ), (44082267329063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183064677/10000000000 : ℝ)|^8301 ≤ (6630798907583/50000000000000 : ℝ)^6253
        have hw : |(-2183064677/10000000000 : ℝ)|=(2183064677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263461517/10000000000 : ℝ)|^8301 ≤ (42656134839307/100000000000000 : ℝ)^6253
        have hw : |(5263461517/10000000000 : ℝ)|=(5263461517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348870211/2500000000 : ℝ)|^8301 ≤ (44082267329063/100000000000000 : ℝ)^6253
        have hw : |(1348870211/2500000000 : ℝ)|=(1348870211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s5_5 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655941977/5000000000 : ℝ)*x 0 + (-211804947/1000000000 : ℝ)*x 1 + (1079096111/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655941977/5000000000 : ℝ)^8301 ≤ (43177871234479/100000000000000 : ℝ)^6253 := by
    have hnat : (2655941977 : ℕ)^8301*100000000000000^6253 ≤ 43177871234479^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655941977 5000000000 43177871234479 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211804947/1000000000 : ℝ)^8301 ≤ (6369932276679/50000000000000 : ℝ)^6253 := by
    have hnat : (211804947 : ℕ)^8301*50000000000000^6253 ≤ 6369932276679^6253*1000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211804947 1000000000 6369932276679 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079096111/2000000000 : ℝ)^8301 ≤ (1763290567781/4000000000000 : ℝ)^6253 := by
    have hnat : (1079096111 : ℕ)^8301*4000000000000^6253 ≤ 1763290567781^6253*2000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079096111 2000000000 1763290567781 4000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655941977/5000000000 : ℝ), (-211804947/1000000000 : ℝ), (1079096111/2000000000 : ℝ)] ![(43177871234479/100000000000000 : ℝ), (6369932276679/50000000000000 : ℝ), (1763290567781/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655941977/5000000000 : ℝ)|^8301 ≤ (43177871234479/100000000000000 : ℝ)^6253
        have hw : |(2655941977/5000000000 : ℝ)|=(2655941977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211804947/1000000000 : ℝ)|^8301 ≤ (6369932276679/50000000000000 : ℝ)^6253
        have hw : |(-211804947/1000000000 : ℝ)|=(211804947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079096111/2000000000 : ℝ)|^8301 ≤ (1763290567781/4000000000000 : ℝ)^6253
        have hw : |(1079096111/2000000000 : ℝ)|=(1079096111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s5_6 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655941919/5000000000 : ℝ)*x 0 + (2697740461/5000000000 : ℝ)*x 1 + (-264756141/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655941919/5000000000 : ℝ)^8301 ≤ (43177869982743/100000000000000 : ℝ)^6253 := by
    have hnat : (2655941919 : ℕ)^8301*100000000000000^6253 ≤ 43177869982743^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655941919 5000000000 43177869982743 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697740461/5000000000 : ℝ)^8301 ≤ (44082268175063/100000000000000 : ℝ)^6253 := by
    have hnat : (2697740461 : ℕ)^8301*100000000000000^6253 ≤ 44082268175063^6253*5000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697740461 5000000000 44082268175063 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264756141/1250000000 : ℝ)^8301 ≤ (6369930911257/50000000000000 : ℝ)^6253 := by
    have hnat : (264756141 : ℕ)^8301*50000000000000^6253 ≤ 6369930911257^6253*1250000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264756141 1250000000 6369930911257 50000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655941919/5000000000 : ℝ), (2697740461/5000000000 : ℝ), (-264756141/1250000000 : ℝ)] ![(43177869982743/100000000000000 : ℝ), (44082268175063/100000000000000 : ℝ), (6369930911257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655941919/5000000000 : ℝ)|^8301 ≤ (43177869982743/100000000000000 : ℝ)^6253
        have hw : |(2655941919/5000000000 : ℝ)|=(2655941919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697740461/5000000000 : ℝ)|^8301 ≤ (44082268175063/100000000000000 : ℝ)^6253
        have hw : |(2697740461/5000000000 : ℝ)|=(2697740461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-264756141/1250000000 : ℝ)|^8301 ≤ (6369930911257/50000000000000 : ℝ)^6253
        have hw : |(-264756141/1250000000 : ℝ)|=(264756141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1108_s5_7 (p : ℝ) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369386099/10000000000 : ℝ)*x 0 + (4501799991/10000000000 : ℝ)*x 1 + (4240900653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369386099/10000000000 : ℝ)^8301 ≤ (6663154941813/20000000000000 : ℝ)^6253 := by
    have hnat : (4369386099 : ℕ)^8301*20000000000000^6253 ≤ 6663154941813^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369386099 10000000000 6663154941813 20000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501799991/10000000000 : ℝ)^8301 ≤ (34662691038197/100000000000000 : ℝ)^6253 := by
    have hnat : (4501799991 : ℕ)^8301*100000000000000^6253 ≤ 34662691038197^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501799991 10000000000 34662691038197 100000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4240900653/10000000000 : ℝ)^8301 ≤ (8005383559817/25000000000000 : ℝ)^6253 := by
    have hnat : (4240900653 : ℕ)^8301*25000000000000^6253 ≤ 8005383559817^6253*10000000000^8301 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240900653 10000000000 8005383559817 25000000000000 8301 6253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8301/2048 : ℝ)) 8301 6253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369386099/10000000000 : ℝ), (4501799991/10000000000 : ℝ), (4240900653/10000000000 : ℝ)] ![(6663154941813/20000000000000 : ℝ), (34662691038197/100000000000000 : ℝ), (8005383559817/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369386099/10000000000 : ℝ)|^8301 ≤ (6663154941813/20000000000000 : ℝ)^6253
        have hw : |(4369386099/10000000000 : ℝ)|=(4369386099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501799991/10000000000 : ℝ)|^8301 ≤ (34662691038197/100000000000000 : ℝ)^6253
        have hw : |(4501799991/10000000000 : ℝ)|=(4501799991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4240900653/10000000000 : ℝ)|^8301 ≤ (8005383559817/25000000000000 : ℝ)^6253
        have hw : |(4240900653/10000000000 : ℝ)|=(4240900653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1108_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (352/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (563/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11109/100000 : ℝ) ^ (2075/512 : ℝ) ≤ (2712714748477467/20000000000000000000 : ℝ) := by
    have hpowers : (11109/100000 : ℝ)^2075 ≤ (2712714748477467/20000000000000000000 : ℝ)^512 := by
      have hnat : (11109 : ℕ)^2075*20000000000000000000^512 ≤ 2712714748477467^512*100000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11109 100000 2712714748477467 20000000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11109/100000 : ℝ)) (X := (2712714748477467/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (2075/512 : ℝ) ≤ (4635148247837403/12500000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^2075 ≤ (4635148247837403/12500000000000000000 : ℝ)^512 := by
      have hnat : (7119 : ℕ)^2075*12500000000000000000^512 ≤ 4635148247837403^512*50000^2075 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 4635148247837403 12500000000000000000 2075 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (4635148247837403/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002712714748477467/10000000000000000000 : ℝ) ≤ (5000334642908801/5000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (10002712714748477467/10000000000000000000 : ℝ)^512 ≤ (5000334642908801/5000000000000000 : ℝ)^2075 := by
      have hnat : (10002712714748477467 : ℕ)^512*5000000000000000^2075 ≤ 5000334642908801^2075*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002712714748477467 10000000000000000000 5000334642908801 5000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000334642908801/5000000000000000 : ℝ)) (X := (10002712714748477467/10000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050644759725086559/100000000000000000000 : ℝ) ≤ (10001249405903177/10000000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (100050644759725086559/100000000000000000000 : ℝ)^512 ≤ (10001249405903177/10000000000000000 : ℝ)^2075 := by
      have hnat : (100050644759725086559 : ℕ)^512*10000000000000000^2075 ≤ 10001249405903177^2075*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050644759725086559 100000000000000000000 10001249405903177 10000000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001249405903177/10000000000000000 : ℝ)) (X := (100050644759725086559/100000000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254635148247837403/6250000000000000000 : ℝ) ≤ (625114345374297/625000000000000 : ℝ) ^ (2075/512 : ℝ) := by
    have hpowers : (6254635148247837403/6250000000000000000 : ℝ)^512 ≤ (625114345374297/625000000000000 : ℝ)^2075 := by
      have hnat : (6254635148247837403 : ℕ)^512*625000000000000^2075 ≤ 625114345374297^2075*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254635148247837403 6250000000000000000 625114345374297 625000000000000 512 2075 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625114345374297/625000000000000 : ℝ)) (X := (6254635148247837403/6250000000000000000 : ℝ)) (by norm_num) 2075 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2712714748477467/20000000000000000000 : ℝ) ≤ ((372371489134071087/372500000000000000 : ℝ)+2*(23204803423/12516000000000 : ℝ)*(11109/100000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (372371489134071087/372500000000000000 : ℝ)+2*(23204803423/12516000000000 : ℝ)*(11109/100000 : ℝ)=(5000334642908801/5000000000000000 : ℝ) by norm_num, show 1+2*(2712714748477467/20000000000000000000 : ℝ)=(10002712714748477467/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4635148247837403/12500000000000000000 : ℝ)+(2712714748477467/20000000000000000000 : ℝ) ≤ ((372371489134071087/372500000000000000 : ℝ)+(23204803423/12516000000000 : ℝ)*((7119/50000 : ℝ)+(11109/100000 : ℝ)))^(2075/512 : ℝ) := by
    rw [show (372371489134071087/372500000000000000 : ℝ)+(23204803423/12516000000000 : ℝ)*((7119/50000 : ℝ)+(11109/100000 : ℝ))=(10001249405903177/10000000000000000 : ℝ) by norm_num, show 1+(4635148247837403/12500000000000000000 : ℝ)+(2712714748477467/20000000000000000000 : ℝ)=(100050644759725086559/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4635148247837403/12500000000000000000 : ℝ) ≤ ((372371489134071087/372500000000000000 : ℝ)+2*(23204803423/12516000000000 : ℝ)*(7119/50000 : ℝ))^(2075/512 : ℝ) := by
    rw [show (372371489134071087/372500000000000000 : ℝ)+2*(23204803423/12516000000000 : ℝ)*(7119/50000 : ℝ)=(625114345374297/625000000000000 : ℝ) by norm_num, show 1+2*(4635148247837403/12500000000000000000 : ℝ)=(6254635148247837403/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (372371489134071087/372500000000000000 : ℝ)*(X 1 0+X 2 0)+(23204803423/12516000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (11109/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (372371489134071087/372500000000000000 : ℝ)) (alpha := (23204803423/12516000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (372371489134071087/372500000000000000 : ℝ)*(X 0 1+X 2 1)+(23204803423/12516000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (11109/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (372371489134071087/372500000000000000 : ℝ)) (alpha := (23204803423/12516000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (372371489134071087/372500000000000000 : ℝ)*(X 0 2+X 1 2)+(23204803423/12516000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2075/512 : ℝ)) (lo := (11109/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (372371489134071087/372500000000000000 : ℝ)) (alpha := (23204803423/12516000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2183059303/10000000000 : ℝ)*X 0 0+(5395825869/10000000000 : ℝ)*X 0 1+(5263117703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345420221/10000000000 : ℝ)*X 1 0+(-2250412603/10000000000 : ℝ)*X 1 1+(263155851/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345419387/10000000000 : ℝ)*X 2 0+(5263117349/10000000000 : ℝ)*X 2 1+(-2250413277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369375321/10000000000 : ℝ)*X 0 0+(848043659/2000000000 : ℝ)*X 0 1+(180099191/400000000 : ℝ)*X 0 2+(4369375321/10000000000 : ℝ)*X 1 0+(848043659/2000000000 : ℝ)*X 1 1+(180099191/400000000 : ℝ)*X 1 2+(4369375321/10000000000 : ℝ)*X 2 0+(848043659/2000000000 : ℝ)*X 2 1+(180099191/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2183064677/10000000000 : ℝ)*X 0 0+(5263461517/10000000000 : ℝ)*X 0 1+(1348870211/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655941977/5000000000 : ℝ)*X 1 0+(-211804947/1000000000 : ℝ)*X 1 1+(1079096111/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655941919/5000000000 : ℝ)*X 2 0+(2697740461/5000000000 : ℝ)*X 2 1+(-264756141/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369386099/10000000000 : ℝ)*X 0 0+(4501799991/10000000000 : ℝ)*X 0 1+(4240900653/10000000000 : ℝ)*X 0 2+(4369386099/10000000000 : ℝ)*X 1 0+(4501799991/10000000000 : ℝ)*X 1 1+(4240900653/10000000000 : ℝ)*X 1 2+(4369386099/10000000000 : ℝ)*X 2 0+(4501799991/10000000000 : ℝ)*X 2 1+(4240900653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1108_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (729310094113099266522036927/65187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (622777707/50000000000000 : ℝ)*(base19) + (742229443/100000000000000 : ℝ)*(base23) + (17373699/50000000000000 : ℝ)*(upper3) + (219646023/50000000000000 : ℝ)*(lower4) + (5674196691639199/100000000000000 : ℝ)*(major0) + (5674196691639199/100000000000000 : ℝ)*(major1) + (5674196691639199/100000000000000 : ℝ)*(major2) + (7535361468049059/100000000000000 : ℝ)*(sp0) + (188384082230643/2500000000000 : ℝ)*(sp1) + (7535339969596231/100000000000000 : ℝ)*(sp2) + (953253400849057/25000000000000 : ℝ)*(sp3) + (1533366037/50000000000000 : ℝ)*(sp4) + (1191147773/5000000000000 : ℝ)*(sp6) + (1487217161/10000000000000 : ℝ)*(sp7) + (1906514237783919/50000000000000 : ℝ)*(f.failure) + (3767682267390567/50000000000000 : ℝ)*(f.sum) + (3528666506951/1564500000000000000000000000 : ℝ)*base66 + (6329239716624400573/782250000000000000000000000000000 : ℝ)*base67 + (1976032809960400573/782250000000000000000000000000000 : ℝ)*base69 + (2563278467493349427/782250000000000000000000000000000 : ℝ)*base72 + (4379151533839/625800000000000000000000000 : ℝ)*base73 + (2515024597649650573/782250000000000000000000000000000 : ℝ)*base75 + (5262270933093400573/782250000000000000000000000000000 : ℝ)*base77 + (12567728672851900573/782250000000000000000000000000000 : ℝ)*base79 + (8596975786429/1564500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (10047641/5000000000000000000000 : ℝ)*base90 + (10047641/5000000000000000000000 : ℝ)*base92 + (10047641/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1059185145575222532030605953/130375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (237708967/50000000000000 : ℝ)*(base19) + (918009/195312500000 : ℝ)*(base23) + (48150869/20000000000000 : ℝ)*(lower2) + (11929153/5000000000000 : ℝ)*(lower4) + (173764641/100000000000000 : ℝ)*(lower5) + (5703771804160861/100000000000000 : ℝ)*(major0) + (5703771804160861/100000000000000 : ℝ)*(major1) + (5703771804160861/100000000000000 : ℝ)*(major2) + (25993345963/100000000000000 : ℝ)*(sp2) + (8824419/500000000000 : ℝ)*(sp3) + (7574640551567977/100000000000000 : ℝ)*(sp4) + (3787320038075021/50000000000000 : ℝ)*(sp5) + (3787307044100703/50000000000000 : ℝ)*(sp6) + (3832901021065169/100000000000000 : ℝ)*(sp7) + (479112848243621/12500000000000 : ℝ)*(f.failure) + (7574640551567977/100000000000000 : ℝ)*(f.sum) + (16272893343857/3129000000000000000000000000 : ℝ)*base65 + (3624102824811480953/782250000000000000000000000000000 : ℝ)*base68 + (1798643982675269047/782250000000000000000000000000000 : ℝ)*base69 + (9504136080583769047/782250000000000000000000000000000 : ℝ)*base71 + (2797990424921/782250000000000000000000000 : ℝ)*base73 + (4297071692890769047/782250000000000000000000000000000 : ℝ)*base75 + (7593541426211519047/782250000000000000000000000000000 : ℝ)*base77 + (1153716108058980953/782250000000000000000000000000000 : ℝ)*base80 + (4488768035287/3129000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (8094419/1250000000000000000000 : ℝ)*base90 + (8094419/1250000000000000000000 : ℝ)*base92 + (8094419/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1108_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1108_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1108_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8303/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1108_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1108_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1108_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2075/512 : ℝ) ≤ p) (hpb : p ≤ (8301/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148810761/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8303/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (352/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1108_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

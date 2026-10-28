-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1079_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:48:27.221401+00:00
-- url     : https://prove2.me/submissions/e0df3afb-7f9f-4463-8240-6d07edcfdc25

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
theorem support_rectangle_w1079_s3_0 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1096410087/5000000000 : ℝ)*x 0 + (2718013747/5000000000 : ℝ)*x 1 + (5225775373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1096410087/5000000000 : ℝ)^517 ≤ (6654735947587/50000000000000 : ℝ)^389 := by
    have hnat : (1096410087 : ℕ)^517*50000000000000^389 ≤ 6654735947587^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096410087 5000000000 6654735947587 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718013747/5000000000 : ℝ)^517 ≤ (1390037119149/3125000000000 : ℝ)^389 := by
    have hnat : (2718013747 : ℕ)^517*3125000000000^389 ≤ 1390037119149^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718013747 5000000000 1390037119149 3125000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5225775373/10000000000 : ℝ)^517 ≤ (8441868054659/20000000000000 : ℝ)^389 := by
    have hnat : (5225775373 : ℕ)^517*20000000000000^389 ≤ 8441868054659^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225775373 10000000000 8441868054659 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1096410087/5000000000 : ℝ), (2718013747/5000000000 : ℝ), (5225775373/10000000000 : ℝ)] ![(6654735947587/50000000000000 : ℝ), (1390037119149/3125000000000 : ℝ), (8441868054659/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1096410087/5000000000 : ℝ)|^517 ≤ (6654735947587/50000000000000 : ℝ)^389
        have hw : |(-1096410087/5000000000 : ℝ)|=(1096410087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718013747/5000000000 : ℝ)|^517 ≤ (1390037119149/3125000000000 : ℝ)^389
        have hw : |(2718013747/5000000000 : ℝ)|=(2718013747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5225775373/10000000000 : ℝ)|^517 ≤ (8441868054659/20000000000000 : ℝ)^389
        have hw : |(5225775373/10000000000 : ℝ)|=(5225775373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s3_1 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5355355731/10000000000 : ℝ)*x 0 + (-2300451221/10000000000 : ℝ)*x 1 + (163305481/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355355731/10000000000 : ℝ)^517 ≤ (43606018639887/100000000000000 : ℝ)^389 := by
    have hnat : (5355355731 : ℕ)^517*100000000000000^389 ≤ 43606018639887^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355355731 10000000000 43606018639887 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2300451221/10000000000 : ℝ)^517 ≤ (14184640856433/100000000000000 : ℝ)^389 := by
    have hnat : (2300451221 : ℕ)^517*100000000000000^389 ≤ 14184640856433^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2300451221 10000000000 14184640856433 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163305481/312500000 : ℝ)^517 ≤ (21104670238629/50000000000000 : ℝ)^389 := by
    have hnat : (163305481 : ℕ)^517*50000000000000^389 ≤ 21104670238629^389*312500000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163305481 312500000 21104670238629 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355355731/10000000000 : ℝ), (-2300451221/10000000000 : ℝ), (163305481/312500000 : ℝ)] ![(43606018639887/100000000000000 : ℝ), (14184640856433/100000000000000 : ℝ), (21104670238629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355355731/10000000000 : ℝ)|^517 ≤ (43606018639887/100000000000000 : ℝ)^389
        have hw : |(5355355731/10000000000 : ℝ)|=(5355355731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2300451221/10000000000 : ℝ)|^517 ≤ (14184640856433/100000000000000 : ℝ)^389
        have hw : |(-2300451221/10000000000 : ℝ)|=(2300451221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163305481/312500000 : ℝ)|^517 ≤ (21104670238629/50000000000000 : ℝ)^389
        have hw : |(163305481/312500000 : ℝ)|=(163305481/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s3_2 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1338838919/2500000000 : ℝ)*x 0 + (26128879/50000000 : ℝ)*x 1 + (-2300450761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338838919/2500000000 : ℝ)^517 ≤ (43606018044689/100000000000000 : ℝ)^389 := by
    have hnat : (1338838919 : ℕ)^517*100000000000000^389 ≤ 43606018044689^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338838919 2500000000 43606018044689 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26128879/50000000 : ℝ)^517 ≤ (8441868971421/20000000000000 : ℝ)^389 := by
    have hnat : (26128879 : ℕ)^517*20000000000000^389 ≤ 8441868971421^389*50000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26128879 50000000 8441868971421 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2300450761/10000000000 : ℝ)^517 ≤ (3546159271689/25000000000000 : ℝ)^389 := by
    have hnat : (2300450761 : ℕ)^517*25000000000000^389 ≤ 3546159271689^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2300450761 10000000000 3546159271689 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338838919/2500000000 : ℝ), (26128879/50000000 : ℝ), (-2300450761/10000000000 : ℝ)] ![(43606018044689/100000000000000 : ℝ), (8441868971421/20000000000000 : ℝ), (3546159271689/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338838919/2500000000 : ℝ)|^517 ≤ (43606018044689/100000000000000 : ℝ)^389
        have hw : |(1338838919/2500000000 : ℝ)|=(1338838919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26128879/50000000 : ℝ)|^517 ≤ (8441868971421/20000000000000 : ℝ)^389
        have hw : |(26128879/50000000 : ℝ)|=(26128879/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2300450761/10000000000 : ℝ)|^517 ≤ (3546159271689/25000000000000 : ℝ)^389
        have hw : |(-2300450761/10000000000 : ℝ)|=(2300450761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s3_3 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4370925063/10000000000 : ℝ)*x 0 + (521160387/1250000000 : ℝ)*x 1 + (4582410471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370925063/10000000000 : ℝ)^517 ≤ (16644641491211/50000000000000 : ℝ)^389 := by
    have hnat : (4370925063 : ℕ)^517*50000000000000^389 ≤ 16644641491211^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370925063 10000000000 16644641491211 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521160387/1250000000 : ℝ)^517 ≤ (31263890655941/100000000000000 : ℝ)^389 := by
    have hnat : (521160387 : ℕ)^517*100000000000000^389 ≤ 31263890655941^389*1250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521160387 1250000000 31263890655941 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4582410471/10000000000 : ℝ)^517 ≤ (1772341317479/5000000000000 : ℝ)^389 := by
    have hnat : (4582410471 : ℕ)^517*5000000000000^389 ≤ 1772341317479^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582410471 10000000000 1772341317479 5000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370925063/10000000000 : ℝ), (521160387/1250000000 : ℝ), (4582410471/10000000000 : ℝ)] ![(16644641491211/50000000000000 : ℝ), (31263890655941/100000000000000 : ℝ), (1772341317479/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370925063/10000000000 : ℝ)|^517 ≤ (16644641491211/50000000000000 : ℝ)^389
        have hw : |(4370925063/10000000000 : ℝ)|=(4370925063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521160387/1250000000 : ℝ)|^517 ≤ (31263890655941/100000000000000 : ℝ)^389
        have hw : |(521160387/1250000000 : ℝ)|=(521160387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4582410471/10000000000 : ℝ)|^517 ≤ (1772341317479/5000000000000 : ℝ)^389
        have hw : |(4582410471/10000000000 : ℝ)|=(4582410471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s3_4 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1096421149/5000000000 : ℝ)*x 0 + (1306657193/2500000000 : ℝ)*x 1 + (1087033729/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1096421149/5000000000 : ℝ)^517 ≤ (3327412591077/25000000000000 : ℝ)^389 := by
    have hnat : (1096421149 : ℕ)^517*25000000000000^389 ≤ 3327412591077^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096421149 5000000000 3327412591077 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306657193/2500000000 : ℝ)^517 ≤ (42218501688487/100000000000000 : ℝ)^389 := by
    have hnat : (1306657193 : ℕ)^517*100000000000000^389 ≤ 42218501688487^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306657193 2500000000 42218501688487 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087033729/2000000000 : ℝ)^517 ≤ (22235923967441/50000000000000 : ℝ)^389 := by
    have hnat : (1087033729 : ℕ)^517*50000000000000^389 ≤ 22235923967441^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087033729 2000000000 22235923967441 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1096421149/5000000000 : ℝ), (1306657193/2500000000 : ℝ), (1087033729/2000000000 : ℝ)] ![(3327412591077/25000000000000 : ℝ), (42218501688487/100000000000000 : ℝ), (22235923967441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1096421149/5000000000 : ℝ)|^517 ≤ (3327412591077/25000000000000 : ℝ)^389
        have hw : |(-1096421149/5000000000 : ℝ)|=(1096421149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1306657193/2500000000 : ℝ)|^517 ≤ (42218501688487/100000000000000 : ℝ)^389
        have hw : |(1306657193/2500000000 : ℝ)|=(1306657193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087033729/2000000000 : ℝ)|^517 ≤ (22235923967441/50000000000000 : ℝ)^389
        have hw : |(1087033729/2000000000 : ℝ)|=(1087033729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s3_5 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (165698137/312500000 : ℝ)*x 0 + (-209105849/1000000000 : ℝ)*x 1 + (5435168497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165698137/312500000 : ℝ)^517 ≤ (5379154281757/12500000000000 : ℝ)^389 := by
    have hnat : (165698137 : ℕ)^517*12500000000000^389 ≤ 5379154281757^389*312500000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165698137 312500000 5379154281757 12500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209105849/1000000000 : ℝ)^517 ≤ (1561864924501/12500000000000 : ℝ)^389 := by
    have hnat : (209105849 : ℕ)^517*12500000000000^389 ≤ 1561864924501^389*1000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209105849 1000000000 1561864924501 12500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435168497/10000000000 : ℝ)^517 ≤ (22235923162721/50000000000000 : ℝ)^389 := by
    have hnat : (5435168497 : ℕ)^517*50000000000000^389 ≤ 22235923162721^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435168497 10000000000 22235923162721 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165698137/312500000 : ℝ), (-209105849/1000000000 : ℝ), (5435168497/10000000000 : ℝ)] ![(5379154281757/12500000000000 : ℝ), (1561864924501/12500000000000 : ℝ), (22235923162721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165698137/312500000 : ℝ)|^517 ≤ (5379154281757/12500000000000 : ℝ)^389
        have hw : |(165698137/312500000 : ℝ)|=(165698137/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-209105849/1000000000 : ℝ)|^517 ≤ (1561864924501/12500000000000 : ℝ)^389
        have hw : |(-209105849/1000000000 : ℝ)|=(209105849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435168497/10000000000 : ℝ)|^517 ≤ (22235923162721/50000000000000 : ℝ)^389
        have hw : |(5435168497/10000000000 : ℝ)|=(5435168497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s3_6 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2651170359/5000000000 : ℝ)*x 0 + (1358792263/2500000000 : ℝ)*x 1 + (-2091057277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651170359/5000000000 : ℝ)^517 ≤ (43033237856721/100000000000000 : ℝ)^389 := by
    have hnat : (2651170359 : ℕ)^517*100000000000000^389 ≤ 43033237856721^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651170359 5000000000 43033237856721 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358792263/2500000000 : ℝ)^517 ≤ (44471852360843/100000000000000 : ℝ)^389 := by
    have hnat : (1358792263 : ℕ)^517*100000000000000^389 ≤ 44471852360843^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358792263 2500000000 44471852360843 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2091057277/10000000000 : ℝ)^517 ≤ (3123727440711/25000000000000 : ℝ)^389 := by
    have hnat : (2091057277 : ℕ)^517*25000000000000^389 ≤ 3123727440711^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091057277 10000000000 3123727440711 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651170359/5000000000 : ℝ), (1358792263/2500000000 : ℝ), (-2091057277/10000000000 : ℝ)] ![(43033237856721/100000000000000 : ℝ), (44471852360843/100000000000000 : ℝ), (3123727440711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651170359/5000000000 : ℝ)|^517 ≤ (43033237856721/100000000000000 : ℝ)^389
        have hw : |(2651170359/5000000000 : ℝ)|=(2651170359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358792263/2500000000 : ℝ)|^517 ≤ (44471852360843/100000000000000 : ℝ)^389
        have hw : |(1358792263/2500000000 : ℝ)|=(1358792263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2091057277/10000000000 : ℝ)|^517 ≤ (3123727440711/25000000000000 : ℝ)^389
        have hw : |(-2091057277/10000000000 : ℝ)|=(2091057277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s3_7 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4370966687/10000000000 : ℝ)*x 0 + (4580734021/10000000000 : ℝ)*x 1 + (4170969991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370966687/10000000000 : ℝ)^517 ≤ (33289704306729/100000000000000 : ℝ)^389 := by
    have hnat : (4370966687 : ℕ)^517*100000000000000^389 ≤ 33289704306729^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370966687 10000000000 33289704306729 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4580734021/10000000000 : ℝ)^517 ≤ (35429592243069/100000000000000 : ℝ)^389 := by
    have hnat : (4580734021 : ℕ)^517*100000000000000^389 ≤ 35429592243069^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4580734021 10000000000 35429592243069 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170969991/10000000000 : ℝ)^517 ≤ (7820175859051/25000000000000 : ℝ)^389 := by
    have hnat : (4170969991 : ℕ)^517*25000000000000^389 ≤ 7820175859051^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170969991 10000000000 7820175859051 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370966687/10000000000 : ℝ), (4580734021/10000000000 : ℝ), (4170969991/10000000000 : ℝ)] ![(33289704306729/100000000000000 : ℝ), (35429592243069/100000000000000 : ℝ), (7820175859051/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370966687/10000000000 : ℝ)|^517 ≤ (33289704306729/100000000000000 : ℝ)^389
        have hw : |(4370966687/10000000000 : ℝ)|=(4370966687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4580734021/10000000000 : ℝ)|^517 ≤ (35429592243069/100000000000000 : ℝ)^389
        have hw : |(4580734021/10000000000 : ℝ)|=(4580734021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170969991/10000000000 : ℝ)|^517 ≤ (7820175859051/25000000000000 : ℝ)^389
        have hw : |(4170969991/10000000000 : ℝ)|=(4170969991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1079_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8349/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (10439/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14887/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8349/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (351/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8349/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (351/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8349/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (351/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8349/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (351/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8349/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (351/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8349/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (351/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (351/4000 : ℝ) ^ (8271/2048 : ℝ) ≤ (2698951549390557/50000000000000000000 : ℝ) := by
    have hpowers : (351/4000 : ℝ)^8271 ≤ (2698951549390557/50000000000000000000 : ℝ)^2048 := by
      have hnat : (351 : ℕ)^8271*50000000000000000000^2048 ≤ 2698951549390557^2048*4000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        351 4000 2698951549390557 50000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (351/4000 : ℝ)) (X := (2698951549390557/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8349/50000 : ℝ) ^ (8271/2048 : ℝ) ≤ (72555896995526599/100000000000000000000 : ℝ) := by
    have hpowers : (8349/50000 : ℝ)^8271 ≤ (72555896995526599/100000000000000000000 : ℝ)^2048 := by
      have hnat : (8349 : ℕ)^8271*100000000000000000000^2048 ≤ 72555896995526599^2048*50000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8349 50000 72555896995526599 100000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8349/50000 : ℝ)) (X := (72555896995526599/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002698951549390557/25000000000000000000 : ℝ) ≤ (10000267306410347/10000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (25002698951549390557/25000000000000000000 : ℝ)^2048 ≤ (10000267306410347/10000000000000000 : ℝ)^8271 := by
      have hnat : (25002698951549390557 : ℕ)^2048*10000000000000000^8271 ≤ 10000267306410347^8271*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002698951549390557 25000000000000000000 10000267306410347 10000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000267306410347/10000000000000000 : ℝ)) (X := (25002698951549390557/25000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100077953800094307713/100000000000000000000 : ℝ) ≤ (1000192966491993/1000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (100077953800094307713/100000000000000000000 : ℝ)^2048 ≤ (1000192966491993/1000000000000000 : ℝ)^8271 := by
      have hnat : (100077953800094307713 : ℕ)^2048*1000000000000000^8271 ≤ 1000192966491993^8271*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100077953800094307713 100000000000000000000 1000192966491993 1000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000192966491993/1000000000000000 : ℝ)) (X := (100077953800094307713/100000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50072555896995526599/50000000000000000000 : ℝ) ≤ (10003592023429513/10000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (50072555896995526599/50000000000000000000 : ℝ)^2048 ≤ (10003592023429513/10000000000000000 : ℝ)^8271 := by
      have hnat : (50072555896995526599 : ℕ)^2048*10000000000000000^8271 ≤ 10003592023429513^8271*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50072555896995526599 50000000000000000000 10003592023429513 10000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003592023429513/10000000000000000 : ℝ)) (X := (50072555896995526599/50000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2698951549390557/50000000000000000000 : ℝ) ≤ ((26400981158948665877/26410000000000000000 : ℝ)+2*(1662358509583/792300000000000 : ℝ)*(351/4000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (26400981158948665877/26410000000000000000 : ℝ)+2*(1662358509583/792300000000000 : ℝ)*(351/4000 : ℝ)=(10000267306410347/10000000000000000 : ℝ) by norm_num, show 1+2*(2698951549390557/50000000000000000000 : ℝ)=(25002698951549390557/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(72555896995526599/100000000000000000000 : ℝ)+(2698951549390557/50000000000000000000 : ℝ) ≤ ((26400981158948665877/26410000000000000000 : ℝ)+(1662358509583/792300000000000 : ℝ)*((8349/50000 : ℝ)+(351/4000 : ℝ)))^(8271/2048 : ℝ) := by
    rw [show (26400981158948665877/26410000000000000000 : ℝ)+(1662358509583/792300000000000 : ℝ)*((8349/50000 : ℝ)+(351/4000 : ℝ))=(1000192966491993/1000000000000000 : ℝ) by norm_num, show 1+(72555896995526599/100000000000000000000 : ℝ)+(2698951549390557/50000000000000000000 : ℝ)=(100077953800094307713/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(72555896995526599/100000000000000000000 : ℝ) ≤ ((26400981158948665877/26410000000000000000 : ℝ)+2*(1662358509583/792300000000000 : ℝ)*(8349/50000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (26400981158948665877/26410000000000000000 : ℝ)+2*(1662358509583/792300000000000 : ℝ)*(8349/50000 : ℝ)=(10003592023429513/10000000000000000 : ℝ) by norm_num, show 1+2*(72555896995526599/100000000000000000000 : ℝ)=(50072555896995526599/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26400981158948665877/26410000000000000000 : ℝ)*(X 1 0+X 2 0)+(1662358509583/792300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (351/4000 : ℝ)) (hi := (8349/50000 : ℝ)) (c := (26400981158948665877/26410000000000000000 : ℝ)) (alpha := (1662358509583/792300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26400981158948665877/26410000000000000000 : ℝ)*(X 0 1+X 2 1)+(1662358509583/792300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (351/4000 : ℝ)) (hi := (8349/50000 : ℝ)) (c := (26400981158948665877/26410000000000000000 : ℝ)) (alpha := (1662358509583/792300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26400981158948665877/26410000000000000000 : ℝ)*(X 0 2+X 1 2)+(1662358509583/792300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (351/4000 : ℝ)) (hi := (8349/50000 : ℝ)) (c := (26400981158948665877/26410000000000000000 : ℝ)) (alpha := (1662358509583/792300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1096410087/5000000000 : ℝ)*X 0 0+(2718013747/5000000000 : ℝ)*X 0 1+(5225775373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355355731/10000000000 : ℝ)*X 1 0+(-2300451221/10000000000 : ℝ)*X 1 1+(163305481/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338838919/2500000000 : ℝ)*X 2 0+(26128879/50000000 : ℝ)*X 2 1+(-2300450761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4370925063/10000000000 : ℝ)*X 0 0+(521160387/1250000000 : ℝ)*X 0 1+(4582410471/10000000000 : ℝ)*X 0 2+(4370925063/10000000000 : ℝ)*X 1 0+(521160387/1250000000 : ℝ)*X 1 1+(4582410471/10000000000 : ℝ)*X 1 2+(4370925063/10000000000 : ℝ)*X 2 0+(521160387/1250000000 : ℝ)*X 2 1+(4582410471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1096421149/5000000000 : ℝ)*X 0 0+(1306657193/2500000000 : ℝ)*X 0 1+(1087033729/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165698137/312500000 : ℝ)*X 1 0+(-209105849/1000000000 : ℝ)*X 1 1+(5435168497/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651170359/5000000000 : ℝ)*X 2 0+(1358792263/2500000000 : ℝ)*X 2 1+(-2091057277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370966687/10000000000 : ℝ)*X 0 0+(4580734021/10000000000 : ℝ)*X 0 1+(4170969991/10000000000 : ℝ)*X 0 2+(4370966687/10000000000 : ℝ)*X 1 0+(4580734021/10000000000 : ℝ)*X 1 1+(4170969991/10000000000 : ℝ)*X 1 2+(4370966687/10000000000 : ℝ)*X 2 0+(4580734021/10000000000 : ℝ)*X 2 1+(4170969991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6204942351853194950447/1650625000000000000000000000 : ℝ) := by norm_num
    linear_combination (604629099/50000000000000 : ℝ)*(base19) + (20178583/2500000000000 : ℝ)*(base23) + (38453741/20000000000000 : ℝ)*(lower2) + (14512337/10000000000000 : ℝ)*(upper5) + (1794205851529489/50000000000000 : ℝ)*(major0) + (1794205851529489/50000000000000 : ℝ)*(major1) + (1794205851529489/50000000000000 : ℝ)*(major2) + (4756215556902801/100000000000000 : ℝ)*(sp0) + (4756242350639759/100000000000000 : ℝ)*(sp1) + (1189060833487219/25000000000000 : ℝ)*(sp2) + (1210285197553631/50000000000000 : ℝ)*(sp3) + (5716837879/20000000000000 : ℝ)*(sp4) + (581194239/100000000000000 : ℝ)*(sp5) + (8744613581/100000000000000 : ℝ)*(sp7) + (1210289569860421/50000000000000 : ℝ)*(f.failure) + (1189061035273049/25000000000000 : ℝ)*(f.sum) + (177618258855239/39615000000000000000000000000 : ℝ)*base65 + (19026760148771159441/3961500000000000000000000000000000 : ℝ)*base68 + (13190922908012159441/3961500000000000000000000000000000 : ℝ)*base70 + (2956893726662340559/3961500000000000000000000000000000 : ℝ)*base71 + (52360922342393/19807500000000000000000000000 : ℝ)*base74 + (38638251059136659441/3961500000000000000000000000000000 : ℝ)*base76 + (13631299790145840559/3961500000000000000000000000000000 : ℝ)*base77 + (17767187698119840559/3961500000000000000000000000000000 : ℝ)*base79 + (20317117717919/39615000000000000000000000000 : ℝ)*base81 + (34077421/2500000000000000000000 : ℝ)*base90 + (34077421/2500000000000000000000 : ℝ)*base92 + (34077421/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (877440743883449704085037617/330125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (546340833/100000000000000 : ℝ)*(base19) + (1713583831/100000000000000 : ℝ)*(base23) + (265366323/100000000000000 : ℝ)*(upper2) + (46390403/50000000000000 : ℝ)*(upper3) + (156126973/100000000000000 : ℝ)*(upper5) + (904459548936793/25000000000000 : ℝ)*(major0) + (904459548936793/25000000000000 : ℝ)*(major1) + (904459548936793/25000000000000 : ℝ)*(major2) + (818029959/20000000000000 : ℝ)*(sp1) + (40567515067/100000000000000 : ℝ)*(sp2) + (959049478223723/20000000000000 : ℝ)*(sp4) + (4795242754627987/100000000000000 : ℝ)*(sp5) + (4795205110019717/100000000000000 : ℝ)*(sp6) + (2440428911778901/100000000000000 : ℝ)*(sp7) + (2440428911778901/100000000000000 : ℝ)*(f.failure) + (959049478223723/20000000000000 : ℝ)*(f.sum) + (178297476550321/39615000000000000000000000000 : ℝ)*base65 + (19211570522922887383/1980750000000000000000000000000000 : ℝ)*base67 + (5651148311574137383/1980750000000000000000000000000000 : ℝ)*base69 + (23195568992623637383/1980750000000000000000000000000000 : ℝ)*base71 + (18430724340467/4951875000000000000000000000 : ℝ)*base73 + (7180038283973862617/1980750000000000000000000000000000 : ℝ)*base76 + (29459780110314887383/1980750000000000000000000000000000 : ℝ)*base77 + (8099775252575112617/1980750000000000000000000000000000 : ℝ)*base80 + (169613092967851/39615000000000000000000000000 : ℝ)*base81 + (32955901/5000000000000000000000 : ℝ)*base90 + (32955901/5000000000000000000000 : ℝ)*base92 + (32955901/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1079_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8349/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10439/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14887/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1079_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1079_s4_0 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-439274291/2000000000 : ℝ)*x 0 + (5405098399/10000000000 : ℝ)*x 1 + (5254384103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (439274291/2000000000 : ℝ)^517 ≤ (3334531707823/25000000000000 : ℝ)^389 := by
    have hnat : (439274291 : ℕ)^517*25000000000000^389 ≤ 3334531707823^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439274291 2000000000 3334531707823 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405098399/10000000000 : ℝ)^517 ≤ (44145144204661/100000000000000 : ℝ)^389 := by
    have hnat : (5405098399 : ℕ)^517*100000000000000^389 ≤ 44145144204661^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405098399 10000000000 44145144204661 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254384103/10000000000 : ℝ)^517 ≤ (42516728946897/100000000000000 : ℝ)^389 := by
    have hnat : (5254384103 : ℕ)^517*100000000000000^389 ≤ 42516728946897^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254384103 10000000000 42516728946897 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-439274291/2000000000 : ℝ), (5405098399/10000000000 : ℝ), (5254384103/10000000000 : ℝ)] ![(3334531707823/25000000000000 : ℝ), (44145144204661/100000000000000 : ℝ), (42516728946897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-439274291/2000000000 : ℝ)|^517 ≤ (3334531707823/25000000000000 : ℝ)^389
        have hw : |(-439274291/2000000000 : ℝ)|=(439274291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405098399/10000000000 : ℝ)|^517 ≤ (44145144204661/100000000000000 : ℝ)^389
        have hw : |(5405098399/10000000000 : ℝ)|=(5405098399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254384103/10000000000 : ℝ)|^517 ≤ (42516728946897/100000000000000 : ℝ)^389
        have hw : |(5254384103/10000000000 : ℝ)|=(5254384103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s4_1 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5347683439/10000000000 : ℝ)*x 0 + (-454603433/2000000000 : ℝ)*x 1 + (656797993/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347683439/10000000000 : ℝ)^517 ≤ (43523010292607/100000000000000 : ℝ)^389 := by
    have hnat : (5347683439 : ℕ)^517*100000000000000^389 ≤ 43523010292607^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347683439 10000000000 43523010292607 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454603433/2000000000 : ℝ)^517 ≤ (349006561367/2500000000000 : ℝ)^389 := by
    have hnat : (454603433 : ℕ)^517*2500000000000^389 ≤ 349006561367^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454603433 2000000000 349006561367 2500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656797993/1250000000 : ℝ)^517 ≤ (2657295452311/6250000000000 : ℝ)^389 := by
    have hnat : (656797993 : ℕ)^517*6250000000000^389 ≤ 2657295452311^389*1250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656797993 1250000000 2657295452311 6250000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347683439/10000000000 : ℝ), (-454603433/2000000000 : ℝ), (656797993/1250000000 : ℝ)] ![(43523010292607/100000000000000 : ℝ), (349006561367/2500000000000 : ℝ), (2657295452311/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347683439/10000000000 : ℝ)|^517 ≤ (43523010292607/100000000000000 : ℝ)^389
        have hw : |(5347683439/10000000000 : ℝ)|=(5347683439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-454603433/2000000000 : ℝ)|^517 ≤ (349006561367/2500000000000 : ℝ)^389
        have hw : |(-454603433/2000000000 : ℝ)|=(454603433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656797993/1250000000 : ℝ)|^517 ≤ (2657295452311/6250000000000 : ℝ)^389
        have hw : |(656797993/1250000000 : ℝ)|=(656797993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s4_2 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5347683559/10000000000 : ℝ)*x 0 + (1313595993/2500000000 : ℝ)*x 1 + (-227301697/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347683559/10000000000 : ℝ)^517 ≤ (43523011590609/100000000000000 : ℝ)^389 := by
    have hnat : (5347683559 : ℕ)^517*100000000000000^389 ≤ 43523011590609^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347683559 10000000000 43523011590609 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313595993/2500000000 : ℝ)^517 ≤ (21258363769047/50000000000000 : ℝ)^389 := by
    have hnat : (1313595993 : ℕ)^517*50000000000000^389 ≤ 21258363769047^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313595993 2500000000 21258363769047 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227301697/1000000000 : ℝ)^517 ≤ (13960260862961/100000000000000 : ℝ)^389 := by
    have hnat : (227301697 : ℕ)^517*100000000000000^389 ≤ 13960260862961^389*1000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227301697 1000000000 13960260862961 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347683559/10000000000 : ℝ), (1313595993/2500000000 : ℝ), (-227301697/1000000000 : ℝ)] ![(43523011590609/100000000000000 : ℝ), (21258363769047/50000000000000 : ℝ), (13960260862961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347683559/10000000000 : ℝ)|^517 ≤ (43523011590609/100000000000000 : ℝ)^389
        have hw : |(5347683559/10000000000 : ℝ)|=(5347683559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313595993/2500000000 : ℝ)|^517 ≤ (21258363769047/50000000000000 : ℝ)^389
        have hw : |(1313595993/2500000000 : ℝ)|=(1313595993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-227301697/1000000000 : ℝ)|^517 ≤ (13960260862961/100000000000000 : ℝ)^389
        have hw : |(-227301697/1000000000 : ℝ)|=(227301697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s4_3 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (136657483/312500000 : ℝ)*x 0 + (2113749629/5000000000 : ℝ)*x 1 + (1130910199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136657483/312500000 : ℝ)^517 ≤ (1040958964121/3125000000000 : ℝ)^389 := by
    have hnat : (136657483 : ℕ)^517*3125000000000^389 ≤ 1040958964121^389*312500000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136657483 312500000 1040958964121 3125000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113749629/5000000000 : ℝ)^517 ≤ (796135097441/2500000000000 : ℝ)^389 := by
    have hnat : (2113749629 : ℕ)^517*2500000000000^389 ≤ 796135097441^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113749629 5000000000 796135097441 2500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130910199/2500000000 : ℝ)^517 ≤ (34843909242217/100000000000000 : ℝ)^389 := by
    have hnat : (1130910199 : ℕ)^517*100000000000000^389 ≤ 34843909242217^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130910199 2500000000 34843909242217 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136657483/312500000 : ℝ), (2113749629/5000000000 : ℝ), (1130910199/2500000000 : ℝ)] ![(1040958964121/3125000000000 : ℝ), (796135097441/2500000000000 : ℝ), (34843909242217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136657483/312500000 : ℝ)|^517 ≤ (1040958964121/3125000000000 : ℝ)^389
        have hw : |(136657483/312500000 : ℝ)|=(136657483/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113749629/5000000000 : ℝ)|^517 ≤ (796135097441/2500000000000 : ℝ)^389
        have hw : |(2113749629/5000000000 : ℝ)|=(2113749629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130910199/2500000000 : ℝ)|^517 ≤ (34843909242217/100000000000000 : ℝ)^389
        have hw : |(1130910199/2500000000 : ℝ)|=(1130910199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s4_4 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098189821/5000000000 : ℝ)*x 0 + (1313705859/2500000000 : ℝ)*x 1 + (1351164259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098189821/5000000000 : ℝ)^517 ≤ (3334548227253/25000000000000 : ℝ)^389 := by
    have hnat : (1098189821 : ℕ)^517*25000000000000^389 ≤ 3334548227253^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098189821 5000000000 3334548227253 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313705859/2500000000 : ℝ)^517 ≤ (8504290739239/20000000000000 : ℝ)^389 := by
    have hnat : (1313705859 : ℕ)^517*20000000000000^389 ≤ 8504290739239^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313705859 2500000000 8504290739239 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351164259/2500000000 : ℝ)^517 ≤ (44140353379021/100000000000000 : ℝ)^389 := by
    have hnat : (1351164259 : ℕ)^517*100000000000000^389 ≤ 44140353379021^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351164259 2500000000 44140353379021 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098189821/5000000000 : ℝ), (1313705859/2500000000 : ℝ), (1351164259/2500000000 : ℝ)] ![(3334548227253/25000000000000 : ℝ), (8504290739239/20000000000000 : ℝ), (44140353379021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098189821/5000000000 : ℝ)|^517 ≤ (3334548227253/25000000000000 : ℝ)^389
        have hw : |(-1098189821/5000000000 : ℝ)|=(1098189821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313705859/2500000000 : ℝ)|^517 ≤ (8504290739239/20000000000000 : ℝ)^389
        have hw : |(1313705859/2500000000 : ℝ)|=(1313705859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351164259/2500000000 : ℝ)|^517 ≤ (44140353379021/100000000000000 : ℝ)^389
        have hw : |(1351164259/2500000000 : ℝ)|=(1351164259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s4_5 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5309684751/10000000000 : ℝ)*x 0 + (-1061371723/5000000000 : ℝ)*x 1 + (5404657121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309684751/10000000000 : ℝ)^517 ≤ (21556235864159/50000000000000 : ℝ)^389 := by
    have hnat : (5309684751 : ℕ)^517*50000000000000^389 ≤ 21556235864159^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309684751 10000000000 21556235864159 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061371723/5000000000 : ℝ)^517 ≤ (3186793489273/25000000000000 : ℝ)^389 := by
    have hnat : (1061371723 : ℕ)^517*25000000000000^389 ≤ 3186793489273^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061371723 5000000000 3186793489273 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404657121/10000000000 : ℝ)^517 ≤ (44140354301651/100000000000000 : ℝ)^389 := by
    have hnat : (5404657121 : ℕ)^517*100000000000000^389 ≤ 44140354301651^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404657121 10000000000 44140354301651 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309684751/10000000000 : ℝ), (-1061371723/5000000000 : ℝ), (5404657121/10000000000 : ℝ)] ![(21556235864159/50000000000000 : ℝ), (3186793489273/25000000000000 : ℝ), (44140354301651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309684751/10000000000 : ℝ)|^517 ≤ (21556235864159/50000000000000 : ℝ)^389
        have hw : |(5309684751/10000000000 : ℝ)|=(5309684751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1061371723/5000000000 : ℝ)|^517 ≤ (3186793489273/25000000000000 : ℝ)^389
        have hw : |(-1061371723/5000000000 : ℝ)|=(1061371723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404657121/10000000000 : ℝ)|^517 ≤ (44140354301651/100000000000000 : ℝ)^389
        have hw : |(5404657121/10000000000 : ℝ)|=(5404657121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s4_6 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1327421163/2500000000 : ℝ)*x 0 + (216186279/400000000 : ℝ)*x 1 + (-2122743779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327421163/2500000000 : ℝ)^517 ≤ (5389058832497/12500000000000 : ℝ)^389 := by
    have hnat : (1327421163 : ℕ)^517*12500000000000^389 ≤ 5389058832497^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327421163 2500000000 5389058832497 12500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216186279/400000000 : ℝ)^517 ≤ (22070176358449/50000000000000 : ℝ)^389 := by
    have hnat : (216186279 : ℕ)^517*50000000000000^389 ≤ 22070176358449^389*400000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216186279 400000000 22070176358449 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122743779/10000000000 : ℝ)^517 ≤ (2549435322953/20000000000000 : ℝ)^389 := by
    have hnat : (2122743779 : ℕ)^517*20000000000000^389 ≤ 2549435322953^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122743779 10000000000 2549435322953 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327421163/2500000000 : ℝ), (216186279/400000000 : ℝ), (-2122743779/10000000000 : ℝ)] ![(5389058832497/12500000000000 : ℝ), (22070176358449/50000000000000 : ℝ), (2549435322953/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327421163/2500000000 : ℝ)|^517 ≤ (5389058832497/12500000000000 : ℝ)^389
        have hw : |(1327421163/2500000000 : ℝ)|=(1327421163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216186279/400000000 : ℝ)|^517 ≤ (22070176358449/50000000000000 : ℝ)^389
        have hw : |(216186279/400000000 : ℝ)|=(216186279/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2122743779/10000000000 : ℝ)|^517 ≤ (2549435322953/20000000000000 : ℝ)^389
        have hw : |(-2122743779/10000000000 : ℝ)|=(2122743779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s4_7 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4373054981/10000000000 : ℝ)*x 0 + (4522777261/10000000000 : ℝ)*x 1 + (422836649/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373054981/10000000000 : ℝ)^517 ≤ (16655422011541/50000000000000 : ℝ)^389 := by
    have hnat : (4373054981 : ℕ)^517*50000000000000^389 ≤ 16655422011541^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373054981 10000000000 16655422011541 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4522777261/10000000000 : ℝ)^517 ≤ (34835069369583/100000000000000 : ℝ)^389 := by
    have hnat : (4522777261 : ℕ)^517*100000000000000^389 ≤ 34835069369583^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522777261 10000000000 34835069369583 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422836649/1000000000 : ℝ)^517 ≤ (1592704329201/5000000000000 : ℝ)^389 := by
    have hnat : (422836649 : ℕ)^517*5000000000000^389 ≤ 1592704329201^389*1000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422836649 1000000000 1592704329201 5000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373054981/10000000000 : ℝ), (4522777261/10000000000 : ℝ), (422836649/1000000000 : ℝ)] ![(16655422011541/50000000000000 : ℝ), (34835069369583/100000000000000 : ℝ), (1592704329201/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373054981/10000000000 : ℝ)|^517 ≤ (16655422011541/50000000000000 : ℝ)^389
        have hw : |(4373054981/10000000000 : ℝ)|=(4373054981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4522777261/10000000000 : ℝ)|^517 ≤ (34835069369583/100000000000000 : ℝ)^389
        have hw : |(4522777261/10000000000 : ℝ)|=(4522777261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(422836649/1000000000 : ℝ)|^517 ≤ (1592704329201/5000000000000 : ℝ)^389
        have hw : |(422836649/1000000000 : ℝ)|=(422836649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1079_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14887/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10439/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (221/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14241/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14887/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10439/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14887/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10439/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14887/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10439/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14887/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10439/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14887/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10439/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14887/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10439/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10439/100000 : ℝ) ^ (8271/2048 : ℝ) ≤ (10883814319173261/100000000000000000000 : ℝ) := by
    have hpowers : (10439/100000 : ℝ)^8271 ≤ (10883814319173261/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10439 : ℕ)^8271*100000000000000000000^2048 ≤ 10883814319173261^2048*100000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10439 100000 10883814319173261 100000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10439/100000 : ℝ)) (X := (10883814319173261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14887/100000 : ℝ) ^ (8271/2048 : ℝ) ≤ (22818675971134391/50000000000000000000 : ℝ) := by
    have hpowers : (14887/100000 : ℝ)^8271 ≤ (22818675971134391/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14887 : ℕ)^8271*50000000000000000000^2048 ≤ 22818675971134391^2048*100000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14887 100000 22818675971134391 50000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14887/100000 : ℝ)) (X := (22818675971134391/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010883814319173261/50000000000000000000 : ℝ) ≤ (10000538948776663/10000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (50010883814319173261/50000000000000000000 : ℝ)^2048 ≤ (10000538948776663/10000000000000000 : ℝ)^8271 := by
      have hnat : (50010883814319173261 : ℕ)^2048*10000000000000000^8271 ≤ 10000538948776663^8271*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010883814319173261 50000000000000000000 10000538948776663 10000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538948776663/10000000000000000 : ℝ)) (X := (50010883814319173261/50000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100056521166261442043/100000000000000000000 : ℝ) ≤ (2500349808800809/2500000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (100056521166261442043/100000000000000000000 : ℝ)^2048 ≤ (2500349808800809/2500000000000000 : ℝ)^8271 := by
      have hnat : (100056521166261442043 : ℕ)^2048*2500000000000000^8271 ≤ 2500349808800809^8271*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100056521166261442043 100000000000000000000 2500349808800809 2500000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500349808800809/2500000000000000 : ℝ)) (X := (100056521166261442043/100000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25022818675971134391/25000000000000000000 : ℝ) ≤ (10002259521629809/10000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (25022818675971134391/25000000000000000000 : ℝ)^2048 ≤ (10002259521629809/10000000000000000 : ℝ)^8271 := by
      have hnat : (25022818675971134391 : ℕ)^2048*10000000000000000^8271 ≤ 10002259521629809^8271*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25022818675971134391 25000000000000000000 10002259521629809 10000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002259521629809/10000000000000000 : ℝ)) (X := (25022818675971134391/25000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10883814319173261/100000000000000000000 : ℝ) ≤ ((4446443618414460593/4448000000000000000 : ℝ)+2*(860286426573/444800000000000 : ℝ)*(10439/100000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (4446443618414460593/4448000000000000000 : ℝ)+2*(860286426573/444800000000000 : ℝ)*(10439/100000 : ℝ)=(10000538948776663/10000000000000000 : ℝ) by norm_num, show 1+2*(10883814319173261/100000000000000000000 : ℝ)=(50010883814319173261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22818675971134391/50000000000000000000 : ℝ)+(10883814319173261/100000000000000000000 : ℝ) ≤ ((4446443618414460593/4448000000000000000 : ℝ)+(860286426573/444800000000000 : ℝ)*((14887/100000 : ℝ)+(10439/100000 : ℝ)))^(8271/2048 : ℝ) := by
    rw [show (4446443618414460593/4448000000000000000 : ℝ)+(860286426573/444800000000000 : ℝ)*((14887/100000 : ℝ)+(10439/100000 : ℝ))=(2500349808800809/2500000000000000 : ℝ) by norm_num, show 1+(22818675971134391/50000000000000000000 : ℝ)+(10883814319173261/100000000000000000000 : ℝ)=(100056521166261442043/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22818675971134391/50000000000000000000 : ℝ) ≤ ((4446443618414460593/4448000000000000000 : ℝ)+2*(860286426573/444800000000000 : ℝ)*(14887/100000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (4446443618414460593/4448000000000000000 : ℝ)+2*(860286426573/444800000000000 : ℝ)*(14887/100000 : ℝ)=(10002259521629809/10000000000000000 : ℝ) by norm_num, show 1+2*(22818675971134391/50000000000000000000 : ℝ)=(25022818675971134391/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4446443618414460593/4448000000000000000 : ℝ)*(X 1 0+X 2 0)+(860286426573/444800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (10439/100000 : ℝ)) (hi := (14887/100000 : ℝ)) (c := (4446443618414460593/4448000000000000000 : ℝ)) (alpha := (860286426573/444800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4446443618414460593/4448000000000000000 : ℝ)*(X 0 1+X 2 1)+(860286426573/444800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (10439/100000 : ℝ)) (hi := (14887/100000 : ℝ)) (c := (4446443618414460593/4448000000000000000 : ℝ)) (alpha := (860286426573/444800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4446443618414460593/4448000000000000000 : ℝ)*(X 0 2+X 1 2)+(860286426573/444800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (10439/100000 : ℝ)) (hi := (14887/100000 : ℝ)) (c := (4446443618414460593/4448000000000000000 : ℝ)) (alpha := (860286426573/444800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-439274291/2000000000 : ℝ)*X 0 0+(5405098399/10000000000 : ℝ)*X 0 1+(5254384103/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347683439/10000000000 : ℝ)*X 1 0+(-454603433/2000000000 : ℝ)*X 1 1+(656797993/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347683559/10000000000 : ℝ)*X 2 0+(1313595993/2500000000 : ℝ)*X 2 1+(-227301697/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((136657483/312500000 : ℝ)*X 0 0+(2113749629/5000000000 : ℝ)*X 0 1+(1130910199/2500000000 : ℝ)*X 0 2+(136657483/312500000 : ℝ)*X 1 0+(2113749629/5000000000 : ℝ)*X 1 1+(1130910199/2500000000 : ℝ)*X 1 2+(136657483/312500000 : ℝ)*X 2 0+(2113749629/5000000000 : ℝ)*X 2 1+(1130910199/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1098189821/5000000000 : ℝ)*X 0 0+(1313705859/2500000000 : ℝ)*X 0 1+(1351164259/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309684751/10000000000 : ℝ)*X 1 0+(-1061371723/5000000000 : ℝ)*X 1 1+(5404657121/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327421163/2500000000 : ℝ)*X 2 0+(216186279/400000000 : ℝ)*X 2 1+(-2122743779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373054981/10000000000 : ℝ)*X 0 0+(4522777261/10000000000 : ℝ)*X 0 1+(422836649/1000000000 : ℝ)*X 0 2+(4373054981/10000000000 : ℝ)*X 1 0+(4522777261/10000000000 : ℝ)*X 1 1+(422836649/1000000000 : ℝ)*X 1 2+(4373054981/10000000000 : ℝ)*X 2 0+(4522777261/10000000000 : ℝ)*X 2 1+(422836649/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (259742789128204737861562989/55600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (158023799/50000000000000 : ℝ)*(base19) + (1451569/2000000000000 : ℝ)*(base23) + (68959881/25000000000000 : ℝ)*(lower2) + (1194707/100000000000000 : ℝ)*(upper3) + (66019089/100000000000000 : ℝ)*(lower4) + (1251479222039009/25000000000000 : ℝ)*(major0) + (1251479222039009/25000000000000 : ℝ)*(major1) + (1251479222039009/25000000000000 : ℝ)*(major2) + (3317533573489311/50000000000000 : ℝ)*(sp0) + (1658767427951183/25000000000000 : ℝ)*(sp1) + (165876748881847/2500000000000 : ℝ)*(sp2) + (1688381189994429/50000000000000 : ℝ)*(sp3) + (720218427/25000000000000 : ℝ)*(sp4) + (1212749771/100000000000000 : ℝ)*(sp7) + (844190898184657/25000000000000 : ℝ)*(f.failure) + (6635070027852331/100000000000000 : ℝ)*(f.sum) + (18169693211477/5560000000000000000000000000 : ℝ)*base65 + (354673243737642337/111200000000000000000000000000000 : ℝ)*base67 + (1332298179506442337/111200000000000000000000000000000 : ℝ)*base69 + (63327832705557663/111200000000000000000000000000000 : ℝ)*base72 + (15564573214757/5560000000000000000000000000 : ℝ)*base73 + (287377638621642337/111200000000000000000000000000000 : ℝ)*base75 + (2683322667688042337/111200000000000000000000000000000 : ℝ)*base77 + (482463095995157663/111200000000000000000000000000000 : ℝ)*base80 + (9162311052323/5560000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (17373657/1250000000000000000000 : ℝ)*base90 + (17373657/1250000000000000000000 : ℝ)*base92 + (17373657/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (251510299724030618666953803/44480000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (842524979/50000000000000 : ℝ)*(base19) + (1778891681/100000000000000 : ℝ)*(base23) + (45514083/100000000000000 : ℝ)*(upper3) + (40010381/25000000000000 : ℝ)*(lower4) + (134560503/100000000000000 : ℝ)*(upper5) + (1007067943495657/20000000000000 : ℝ)*(major0) + (1007067943495657/20000000000000 : ℝ)*(major1) + (1007067943495657/20000000000000 : ℝ)*(major2) + (26137523221/50000000000000 : ℝ)*(sp1) + (40658287989/100000000000000 : ℝ)*(sp2) + (1334813670563559/20000000000000 : ℝ)*(sp4) + (1668503598180349/25000000000000 : ℝ)*(sp5) + (3337012957819063/50000000000000 : ℝ)*(sp6) + (3396610893656829/100000000000000 : ℝ)*(sp7) + (3396610893656829/100000000000000 : ℝ)*(f.failure) + (1334813670563559/20000000000000 : ℝ)*(f.sum) + (7967307392629/4448000000000000000000000000 : ℝ)*base65 + (219610012233685399/88960000000000000000000000000000 : ℝ)*base68 + (155515907190954601/88960000000000000000000000000000 : ℝ)*base69 + (300386746508074601/88960000000000000000000000000000 : ℝ)*base71 + (31831759583243/4448000000000000000000000000 : ℝ)*base74 + (199152715923285399/88960000000000000000000000000000 : ℝ)*base76 + (384499263790165399/88960000000000000000000000000000 : ℝ)*base78 + (1271090305214165399/88960000000000000000000000000000 : ℝ)*base80 + (11136138800213/4448000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7689829/5000000000000000000000 : ℝ)*base90 + (7689829/5000000000000000000000 : ℝ)*base92 + (7689829/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1079_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14887/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10439/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (221/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14241/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1079_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1079_s5_0 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2197162803/10000000000 : ℝ)*x 0 + (1349156433/2500000000 : ℝ)*x 1 + (5262337851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2197162803/10000000000 : ℝ)^517 ≤ (13344514218497/100000000000000 : ℝ)^389 := by
    have hnat : (2197162803 : ℕ)^517*100000000000000^389 ≤ 13344514218497^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197162803 10000000000 13344514218497 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349156433/2500000000 : ℝ)^517 ≤ (44053199153763/100000000000000 : ℝ)^389 := by
    have hnat : (1349156433 : ℕ)^517*100000000000000^389 ≤ 44053199153763^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349156433 2500000000 44053199153763 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262337851/10000000000 : ℝ)^517 ≤ (1331321456511/3125000000000 : ℝ)^389 := by
    have hnat : (5262337851 : ℕ)^517*3125000000000^389 ≤ 1331321456511^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262337851 10000000000 1331321456511 3125000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2197162803/10000000000 : ℝ), (1349156433/2500000000 : ℝ), (5262337851/10000000000 : ℝ)] ![(13344514218497/100000000000000 : ℝ), (44053199153763/100000000000000 : ℝ), (1331321456511/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2197162803/10000000000 : ℝ)|^517 ≤ (13344514218497/100000000000000 : ℝ)^389
        have hw : |(-2197162803/10000000000 : ℝ)|=(2197162803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349156433/2500000000 : ℝ)|^517 ≤ (44053199153763/100000000000000 : ℝ)^389
        have hw : |(1349156433/2500000000 : ℝ)|=(1349156433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262337851/10000000000 : ℝ)|^517 ≤ (1331321456511/3125000000000 : ℝ)^389
        have hw : |(5262337851/10000000000 : ℝ)|=(5262337851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s5_1 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2672785987/5000000000 : ℝ)*x 0 + (-2265330197/10000000000 : ℝ)*x 1 + (164448027/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672785987/5000000000 : ℝ)^517 ≤ (43500172724877/100000000000000 : ℝ)^389 := by
    have hnat : (2672785987 : ℕ)^517*100000000000000^389 ≤ 43500172724877^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672785987 5000000000 43500172724877 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265330197/10000000000 : ℝ)^517 ≤ (2779510254341/20000000000000 : ℝ)^389 := by
    have hnat : (2265330197 : ℕ)^517*20000000000000^389 ≤ 2779510254341^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265330197 10000000000 2779510254341 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164448027/312500000 : ℝ)^517 ≤ (42602275988651/100000000000000 : ℝ)^389 := by
    have hnat : (164448027 : ℕ)^517*100000000000000^389 ≤ 42602275988651^389*312500000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164448027 312500000 42602275988651 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672785987/5000000000 : ℝ), (-2265330197/10000000000 : ℝ), (164448027/312500000 : ℝ)] ![(43500172724877/100000000000000 : ℝ), (2779510254341/20000000000000 : ℝ), (42602275988651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672785987/5000000000 : ℝ)|^517 ≤ (43500172724877/100000000000000 : ℝ)^389
        have hw : |(2672785987/5000000000 : ℝ)|=(2672785987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2265330197/10000000000 : ℝ)|^517 ≤ (2779510254341/20000000000000 : ℝ)^389
        have hw : |(-2265330197/10000000000 : ℝ)|=(2265330197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164448027/312500000 : ℝ)|^517 ≤ (42602275988651/100000000000000 : ℝ)^389
        have hw : |(164448027/312500000 : ℝ)|=(164448027/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s5_2 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5345571877/10000000000 : ℝ)*x 0 + (5262337801/10000000000 : ℝ)*x 1 + (-2265329089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345571877/10000000000 : ℝ)^517 ≤ (8700034335159/20000000000000 : ℝ)^389 := by
    have hnat : (5345571877 : ℕ)^517*20000000000000^389 ≤ 8700034335159^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345571877 10000000000 8700034335159 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262337801/10000000000 : ℝ)^517 ≤ (42602286070373/100000000000000 : ℝ)^389 := by
    have hnat : (5262337801 : ℕ)^517*100000000000000^389 ≤ 42602286070373^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262337801 10000000000 42602286070373 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265329089/10000000000 : ℝ)^517 ≤ (868596389847/6250000000000 : ℝ)^389 := by
    have hnat : (2265329089 : ℕ)^517*6250000000000^389 ≤ 868596389847^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265329089 10000000000 868596389847 6250000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345571877/10000000000 : ℝ), (5262337801/10000000000 : ℝ), (-2265329089/10000000000 : ℝ)] ![(8700034335159/20000000000000 : ℝ), (42602286070373/100000000000000 : ℝ), (868596389847/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345571877/10000000000 : ℝ)|^517 ≤ (8700034335159/20000000000000 : ℝ)^389
        have hw : |(5345571877/10000000000 : ℝ)|=(5345571877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262337801/10000000000 : ℝ)|^517 ≤ (42602286070373/100000000000000 : ℝ)^389
        have hw : |(5262337801/10000000000 : ℝ)|=(5262337801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2265329089/10000000000 : ℝ)|^517 ≤ (868596389847/6250000000000 : ℝ)^389
        have hw : |(-2265329089/10000000000 : ℝ)|=(2265329089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s5_3 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (874700037/2000000000 : ℝ)*x 0 + (530447117/1250000000 : ℝ)*x 1 + (901488467/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874700037/2000000000 : ℝ)^517 ≤ (6663070246989/20000000000000 : ℝ)^389 := by
    have hnat : (874700037 : ℕ)^517*20000000000000^389 ≤ 6663070246989^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874700037 2000000000 6663070246989 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530447117/1250000000 : ℝ)^517 ≤ (1600323402931/5000000000000 : ℝ)^389 := by
    have hnat : (530447117 : ℕ)^517*5000000000000^389 ≤ 1600323402931^389*1250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530447117 1250000000 1600323402931 5000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901488467/2000000000 : ℝ)^517 ≤ (34678180696779/100000000000000 : ℝ)^389 := by
    have hnat : (901488467 : ℕ)^517*100000000000000^389 ≤ 34678180696779^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901488467 2000000000 34678180696779 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874700037/2000000000 : ℝ), (530447117/1250000000 : ℝ), (901488467/2000000000 : ℝ)] ![(6663070246989/20000000000000 : ℝ), (1600323402931/5000000000000 : ℝ), (34678180696779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874700037/2000000000 : ℝ)|^517 ≤ (6663070246989/20000000000000 : ℝ)^389
        have hw : |(874700037/2000000000 : ℝ)|=(874700037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530447117/1250000000 : ℝ)|^517 ≤ (1600323402931/5000000000000 : ℝ)^389
        have hw : |(530447117/1250000000 : ℝ)|=(530447117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901488467/2000000000 : ℝ)|^517 ≤ (34678180696779/100000000000000 : ℝ)^389
        have hw : |(901488467/2000000000 : ℝ)|=(901488467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s5_4 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098584247/5000000000 : ℝ)*x 0 + (5262686707/10000000000 : ℝ)*x 1 + (1079255103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098584247/5000000000 : ℝ)^517 ≤ (13344560156303/100000000000000 : ℝ)^389 := by
    have hnat : (1098584247 : ℕ)^517*100000000000000^389 ≤ 13344560156303^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098584247 5000000000 13344560156303 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262686707/10000000000 : ℝ)^517 ≤ (42606040191649/100000000000000 : ℝ)^389 := by
    have hnat : (5262686707 : ℕ)^517*100000000000000^389 ≤ 42606040191649^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262686707 10000000000 42606040191649 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079255103/2000000000 : ℝ)^517 ≤ (11012349908559/25000000000000 : ℝ)^389 := by
    have hnat : (1079255103 : ℕ)^517*25000000000000^389 ≤ 11012349908559^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079255103 2000000000 11012349908559 25000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098584247/5000000000 : ℝ), (5262686707/10000000000 : ℝ), (1079255103/2000000000 : ℝ)] ![(13344560156303/100000000000000 : ℝ), (42606040191649/100000000000000 : ℝ), (11012349908559/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098584247/5000000000 : ℝ)|^517 ≤ (13344560156303/100000000000000 : ℝ)^389
        have hw : |(-1098584247/5000000000 : ℝ)|=(1098584247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262686707/10000000000 : ℝ)|^517 ≤ (42606040191649/100000000000000 : ℝ)^389
        have hw : |(5262686707/10000000000 : ℝ)|=(5262686707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079255103/2000000000 : ℝ)|^517 ≤ (11012349908559/25000000000000 : ℝ)^389
        have hw : |(1079255103/2000000000 : ℝ)|=(1079255103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s5_5 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (663964083/1250000000 : ℝ)*x 0 + (-2131391887/10000000000 : ℝ)*x 1 + (5396275511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663964083/1250000000 : ℝ)^517 ≤ (5391794623683/12500000000000 : ℝ)^389 := by
    have hnat : (663964083 : ℕ)^517*12500000000000^389 ≤ 5391794623683^389*1250000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663964083 1250000000 5391794623683 12500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2131391887/10000000000 : ℝ)^517 ≤ (640812169729/5000000000000 : ℝ)^389 := by
    have hnat : (2131391887 : ℕ)^517*5000000000000^389 ≤ 640812169729^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131391887 10000000000 640812169729 5000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396275511/10000000000 : ℝ)^517 ≤ (1101234989771/2500000000000 : ℝ)^389 := by
    have hnat : (5396275511 : ℕ)^517*2500000000000^389 ≤ 1101234989771^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396275511 10000000000 1101234989771 2500000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663964083/1250000000 : ℝ), (-2131391887/10000000000 : ℝ), (5396275511/10000000000 : ℝ)] ![(5391794623683/12500000000000 : ℝ), (640812169729/5000000000000 : ℝ), (1101234989771/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663964083/1250000000 : ℝ)|^517 ≤ (5391794623683/12500000000000 : ℝ)^389
        have hw : |(663964083/1250000000 : ℝ)|=(663964083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2131391887/10000000000 : ℝ)|^517 ≤ (640812169729/5000000000000 : ℝ)^389
        have hw : |(-2131391887/10000000000 : ℝ)|=(2131391887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396275511/10000000000 : ℝ)|^517 ≤ (1101234989771/2500000000000 : ℝ)^389
        have hw : |(5396275511/10000000000 : ℝ)|=(5396275511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s5_6 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1327928167/2500000000 : ℝ)*x 0 + (5396275509/10000000000 : ℝ)*x 1 + (-426278377/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327928167/2500000000 : ℝ)^517 ≤ (8626871406527/20000000000000 : ℝ)^389 := by
    have hnat : (1327928167 : ℕ)^517*20000000000000^389 ≤ 8626871406527^389*2500000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327928167 2500000000 8626871406527 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396275509/10000000000 : ℝ)^517 ≤ (22024699784571/50000000000000 : ℝ)^389 := by
    have hnat : (5396275509 : ℕ)^517*50000000000000^389 ≤ 22024699784571^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396275509 10000000000 22024699784571 50000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426278377/2000000000 : ℝ)^517 ≤ (12816243378597/100000000000000 : ℝ)^389 := by
    have hnat : (426278377 : ℕ)^517*100000000000000^389 ≤ 12816243378597^389*2000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426278377 2000000000 12816243378597 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327928167/2500000000 : ℝ), (5396275509/10000000000 : ℝ), (-426278377/2000000000 : ℝ)] ![(8626871406527/20000000000000 : ℝ), (22024699784571/50000000000000 : ℝ), (12816243378597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327928167/2500000000 : ℝ)|^517 ≤ (8626871406527/20000000000000 : ℝ)^389
        have hw : |(1327928167/2500000000 : ℝ)|=(1327928167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396275509/10000000000 : ℝ)|^517 ≤ (22024699784571/50000000000000 : ℝ)^389
        have hw : |(5396275509/10000000000 : ℝ)|=(5396275509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426278377/2000000000 : ℝ)|^517 ≤ (12816243378597/100000000000000 : ℝ)^389
        have hw : |(-426278377/2000000000 : ℝ)|=(426278377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1079_s5_7 (p : ℝ) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4373511091/10000000000 : ℝ)*x 0 + (2253378321/5000000000 : ℝ)*x 1 + (169770613/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373511091/10000000000 : ℝ)^517 ≤ (6663092329673/20000000000000 : ℝ)^389 := by
    have hnat : (4373511091 : ℕ)^517*20000000000000^389 ≤ 6663092329673^389*10000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373511091 10000000000 6663092329673 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253378321/5000000000 : ℝ)^517 ≤ (6934233920157/20000000000000 : ℝ)^389 := by
    have hnat : (2253378321 : ℕ)^517*20000000000000^389 ≤ 6934233920157^389*5000000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253378321 5000000000 6934233920157 20000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169770613/400000000 : ℝ)^517 ≤ (32013368742387/100000000000000 : ℝ)^389 := by
    have hnat : (169770613 : ℕ)^517*100000000000000^389 ≤ 32013368742387^389*400000000^517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169770613 400000000 32013368742387 100000000000000 517 389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (517/128 : ℝ)) 517 389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373511091/10000000000 : ℝ), (2253378321/5000000000 : ℝ), (169770613/400000000 : ℝ)] ![(6663092329673/20000000000000 : ℝ), (6934233920157/20000000000000 : ℝ), (32013368742387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373511091/10000000000 : ℝ)|^517 ≤ (6663092329673/20000000000000 : ℝ)^389
        have hw : |(4373511091/10000000000 : ℝ)|=(4373511091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253378321/5000000000 : ℝ)|^517 ≤ (6934233920157/20000000000000 : ℝ)^389
        have hw : |(2253378321/5000000000 : ℝ)|=(2253378321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169770613/400000000 : ℝ)|^517 ≤ (32013368742387/100000000000000 : ℝ)^389
        have hw : |(169770613/400000000 : ℝ)|=(169770613/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1079_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (221/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (11219/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14063/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (221/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (221/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (221/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (221/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (221/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (221/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (221/2000 : ℝ) ^ (8271/2048 : ℝ) ≤ (13694543483175123/100000000000000000000 : ℝ) := by
    have hpowers : (221/2000 : ℝ)^8271 ≤ (13694543483175123/100000000000000000000 : ℝ)^2048 := by
      have hnat : (221 : ℕ)^8271*100000000000000000000^2048 ≤ 13694543483175123^2048*2000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        221 2000 13694543483175123 100000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (221/2000 : ℝ)) (X := (13694543483175123/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14241/100000 : ℝ) ^ (8271/2048 : ℝ) ≤ (38151395774766829/100000000000000000000 : ℝ) := by
    have hpowers : (14241/100000 : ℝ)^8271 ≤ (38151395774766829/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14241 : ℕ)^8271*100000000000000000000^2048 ≤ 38151395774766829^2048*100000^8271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14241 100000 38151395774766829 100000000000000000000 8271 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14241/100000 : ℝ)) (X := (38151395774766829/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013694543483175123/50000000000000000000 : ℝ) ≤ (10000678117173789/10000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (50013694543483175123/50000000000000000000 : ℝ)^2048 ≤ (10000678117173789/10000000000000000 : ℝ)^8271 := by
      have hnat : (50013694543483175123 : ℕ)^2048*10000000000000000^8271 ≤ 10000678117173789^8271*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013694543483175123 50000000000000000000 10000678117173789 10000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000678117173789/10000000000000000 : ℝ)) (X := (50013694543483175123/50000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563310092800905343/1562500000000000000 : ℝ) ≤ (10001283518078743/10000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (1563310092800905343/1562500000000000000 : ℝ)^2048 ≤ (10001283518078743/10000000000000000 : ℝ)^8271 := by
      have hnat : (1563310092800905343 : ℕ)^2048*10000000000000000^8271 ≤ 10001283518078743^8271*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563310092800905343 1562500000000000000 10001283518078743 10000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001283518078743/10000000000000000 : ℝ)) (X := (1563310092800905343/1562500000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038151395774766829/50000000000000000000 : ℝ) ≤ (10001888918983697/10000000000000000 : ℝ) ^ (8271/2048 : ℝ) := by
    have hpowers : (50038151395774766829/50000000000000000000 : ℝ)^2048 ≤ (10001888918983697/10000000000000000 : ℝ)^8271 := by
      have hnat : (50038151395774766829 : ℕ)^2048*10000000000000000^8271 ≤ 10001888918983697^8271*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038151395774766829 50000000000000000000 10001888918983697 10000000000000000 2048 8271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001888918983697/10000000000000000 : ℝ)) (X := (50038151395774766829/50000000000000000000 : ℝ)) (by norm_num) 8271 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13694543483175123/100000000000000000000 : ℝ) ≤ ((31898784511902077299/31910000000000000000 : ℝ)+2*(302700452477/159550000000000 : ℝ)*(221/2000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (31898784511902077299/31910000000000000000 : ℝ)+2*(302700452477/159550000000000 : ℝ)*(221/2000 : ℝ)=(10000678117173789/10000000000000000 : ℝ) by norm_num, show 1+2*(13694543483175123/100000000000000000000 : ℝ)=(50013694543483175123/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38151395774766829/100000000000000000000 : ℝ)+(13694543483175123/100000000000000000000 : ℝ) ≤ ((31898784511902077299/31910000000000000000 : ℝ)+(302700452477/159550000000000 : ℝ)*((14241/100000 : ℝ)+(221/2000 : ℝ)))^(8271/2048 : ℝ) := by
    rw [show (31898784511902077299/31910000000000000000 : ℝ)+(302700452477/159550000000000 : ℝ)*((14241/100000 : ℝ)+(221/2000 : ℝ))=(10001283518078743/10000000000000000 : ℝ) by norm_num, show 1+(38151395774766829/100000000000000000000 : ℝ)+(13694543483175123/100000000000000000000 : ℝ)=(1563310092800905343/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38151395774766829/100000000000000000000 : ℝ) ≤ ((31898784511902077299/31910000000000000000 : ℝ)+2*(302700452477/159550000000000 : ℝ)*(14241/100000 : ℝ))^(8271/2048 : ℝ) := by
    rw [show (31898784511902077299/31910000000000000000 : ℝ)+2*(302700452477/159550000000000 : ℝ)*(14241/100000 : ℝ)=(10001888918983697/10000000000000000 : ℝ) by norm_num, show 1+2*(38151395774766829/100000000000000000000 : ℝ)=(50038151395774766829/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31898784511902077299/31910000000000000000 : ℝ)*(X 1 0+X 2 0)+(302700452477/159550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (221/2000 : ℝ)) (hi := (14241/100000 : ℝ)) (c := (31898784511902077299/31910000000000000000 : ℝ)) (alpha := (302700452477/159550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31898784511902077299/31910000000000000000 : ℝ)*(X 0 1+X 2 1)+(302700452477/159550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (221/2000 : ℝ)) (hi := (14241/100000 : ℝ)) (c := (31898784511902077299/31910000000000000000 : ℝ)) (alpha := (302700452477/159550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31898784511902077299/31910000000000000000 : ℝ)*(X 0 2+X 1 2)+(302700452477/159550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8271/2048 : ℝ)) (lo := (221/2000 : ℝ)) (hi := (14241/100000 : ℝ)) (c := (31898784511902077299/31910000000000000000 : ℝ)) (alpha := (302700452477/159550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2197162803/10000000000 : ℝ)*X 0 0+(1349156433/2500000000 : ℝ)*X 0 1+(5262337851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672785987/5000000000 : ℝ)*X 1 0+(-2265330197/10000000000 : ℝ)*X 1 1+(164448027/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345571877/10000000000 : ℝ)*X 2 0+(5262337801/10000000000 : ℝ)*X 2 1+(-2265329089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874700037/2000000000 : ℝ)*X 0 0+(530447117/1250000000 : ℝ)*X 0 1+(901488467/2000000000 : ℝ)*X 0 2+(874700037/2000000000 : ℝ)*X 1 0+(530447117/1250000000 : ℝ)*X 1 1+(901488467/2000000000 : ℝ)*X 1 2+(874700037/2000000000 : ℝ)*X 2 0+(530447117/1250000000 : ℝ)*X 2 1+(901488467/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1098584247/5000000000 : ℝ)*X 0 0+(5262686707/10000000000 : ℝ)*X 0 1+(1079255103/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663964083/1250000000 : ℝ)*X 1 0+(-2131391887/10000000000 : ℝ)*X 1 1+(5396275511/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327928167/2500000000 : ℝ)*X 2 0+(5396275509/10000000000 : ℝ)*X 2 1+(-426278377/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373511091/10000000000 : ℝ)*X 0 0+(2253378321/5000000000 : ℝ)*X 0 1+(169770613/400000000 : ℝ)*X 0 2+(4373511091/10000000000 : ℝ)*X 1 0+(2253378321/5000000000 : ℝ)*X 1 1+(169770613/400000000 : ℝ)*X 1 2+(4373511091/10000000000 : ℝ)*X 2 0+(2253378321/5000000000 : ℝ)*X 2 1+(169770613/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1079_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8677324526547862677850724619/1595500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2347273193/100000000000000 : ℝ)*(base19) + (1125353117/50000000000000 : ℝ)*(base23) + (1107947/781250000000 : ℝ)*(lower2) + (216715893/100000000000000 : ℝ)*(upper5) + (5618356067842591/100000000000000 : ℝ)*(major0) + (5618356067842591/100000000000000 : ℝ)*(major1) + (5618356067842591/100000000000000 : ℝ)*(major2) + (116355447712233/1562500000000 : ℝ)*(sp0) + (74467744583669/1000000000000 : ℝ)*(sp1) + (7446822527214299/100000000000000 : ℝ)*(sp2) + (9474625172241/250000000000 : ℝ)*(sp3) + (76124337621/100000000000000 : ℝ)*(sp4) + (47972280439/100000000000000 : ℝ)*(sp5) + (37107580761/100000000000000 : ℝ)*(sp7) + (1894943588238581/50000000000000 : ℝ)*(f.failure) + (7446824777920533/100000000000000 : ℝ)*(f.sum) + (97882875701159/15955000000000000000000000000 : ℝ)*base65 + (42911757133564841709/3191000000000000000000000000000000 : ℝ)*base67 + (59491339033695841709/3191000000000000000000000000000000 : ℝ)*base69 + (104148311554550841709/3191000000000000000000000000000000 : ℝ)*base71 + (39302970931081/15955000000000000000000000000 : ℝ)*base74 + (70572472638313841709/3191000000000000000000000000000000 : ℝ)*base75 + (89336873010293841709/3191000000000000000000000000000000 : ℝ)*base77 + (66065586543776841709/3191000000000000000000000000000000 : ℝ)*base79 + (10595098561743/1994375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (23775581/2500000000000000000000 : ℝ)*base90 + (23775581/2500000000000000000000 : ℝ)*base92 + (23775581/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38473730284732059013083/15955000000000000000000000000 : ℝ) := by norm_num
    linear_combination (229794909/50000000000000 : ℝ)*(base19) + (499254649/100000000000000 : ℝ)*(base23) + (49058683/100000000000000 : ℝ)*(upper3) + (14897563/100000000000000 : ℝ)*(lower4) + (48983419/100000000000000 : ℝ)*(upper5) + (5647653260648791/100000000000000 : ℝ)*(major0) + (5647653260648791/100000000000000 : ℝ)*(major1) + (5647653260648791/100000000000000 : ℝ)*(major2) + (5955321641/50000000000000 : ℝ)*(sp1) + (12848974089/100000000000000 : ℝ)*(sp2) + (7485656712195519/100000000000000 : ℝ)*(sp4) + (374282217098121/5000000000000 : ℝ)*(sp5) + (7485643363966781/100000000000000 : ℝ)*(sp6) + (238103108045149/6250000000000 : ℝ)*(sp7) + (238103108045149/6250000000000 : ℝ)*(f.failure) + (7485656712195519/100000000000000 : ℝ)*(f.sum) + (9575314574431/3988750000000000000000000000 : ℝ)*base65 + (8946295383295509/3191000000000000000000000000000000 : ℝ)*base67 + (7284389203199295509/3191000000000000000000000000000000 : ℝ)*base69 + (21525791729537704491/3191000000000000000000000000000000 : ℝ)*base72 + (8056554233607/1994375000000000000000000000 : ℝ)*base74 + (624271299553704491/3191000000000000000000000000000000 : ℝ)*base76 + (22586196810220704491/3191000000000000000000000000000000 : ℝ)*base78 + (53018352413348295509/3191000000000000000000000000000000 : ℝ)*base79 + (20977534838211/3988750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (593149/312500000000000000000 : ℝ)*base90 + (593149/312500000000000000000 : ℝ)*base92 + (593149/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1079_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (221/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1079_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1079_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8349/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1079_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1079_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1079_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8271/2048 : ℝ) ≤ p) (hpb : p ≤ (517/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74122999/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8349/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1079_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

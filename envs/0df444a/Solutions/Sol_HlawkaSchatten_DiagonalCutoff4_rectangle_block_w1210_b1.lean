-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1210_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:07:05.728084+00:00
-- url     : https://prove2.me/submissions/35854df6-c2e5-449c-95d9-b80fbc370c02

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
theorem support_rectangle_w1210_s3_0 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-213166511/1000000000 : ℝ)*x 0 + (1355633211/2500000000 : ℝ)*x 1 + (5238075901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213166511/1000000000 : ℝ)^8403 ≤ (12953525136297/100000000000000 : ℝ)^6355 := by
    have hnat : (213166511 : ℕ)^8403*100000000000000^6355 ≤ 12953525136297^6355*1000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213166511 1000000000 12953525136297 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355633211/2500000000 : ℝ)^8403 ≤ (22259459612311/50000000000000 : ℝ)^6355 := by
    have hnat : (1355633211 : ℕ)^8403*50000000000000^6355 ≤ 22259459612311^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355633211 2500000000 22259459612311 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238075901/10000000000 : ℝ)^8403 ≤ (8505511125717/20000000000000 : ℝ)^6355 := by
    have hnat : (5238075901 : ℕ)^8403*20000000000000^6355 ≤ 8505511125717^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238075901 10000000000 8505511125717 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213166511/1000000000 : ℝ), (1355633211/2500000000 : ℝ), (5238075901/10000000000 : ℝ)] ![(12953525136297/100000000000000 : ℝ), (22259459612311/50000000000000 : ℝ), (8505511125717/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213166511/1000000000 : ℝ)|^8403 ≤ (12953525136297/100000000000000 : ℝ)^6355
        have hw : |(-213166511/1000000000 : ℝ)|=(213166511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355633211/2500000000 : ℝ)|^8403 ≤ (22259459612311/50000000000000 : ℝ)^6355
        have hw : |(1355633211/2500000000 : ℝ)|=(1355633211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238075901/10000000000 : ℝ)|^8403 ≤ (8505511125717/20000000000000 : ℝ)^6355
        have hw : |(5238075901/10000000000 : ℝ)|=(5238075901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s3_1 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338050989/2500000000 : ℝ)*x 0 + (-2225820487/10000000000 : ℝ)*x 1 + (130951901/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338050989/2500000000 : ℝ)^8403 ≤ (10939261048971/25000000000000 : ℝ)^6355 := by
    have hnat : (1338050989 : ℕ)^8403*25000000000000^6355 ≤ 10939261048971^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338050989 2500000000 10939261048971 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2225820487/10000000000 : ℝ)^8403 ≤ (13715398660061/100000000000000 : ℝ)^6355 := by
    have hnat : (2225820487 : ℕ)^8403*100000000000000^6355 ≤ 13715398660061^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225820487 10000000000 13715398660061 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130951901/250000000 : ℝ)^8403 ≤ (42527557120803/100000000000000 : ℝ)^6355 := by
    have hnat : (130951901 : ℕ)^8403*100000000000000^6355 ≤ 42527557120803^6355*250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130951901 250000000 42527557120803 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338050989/2500000000 : ℝ), (-2225820487/10000000000 : ℝ), (130951901/250000000 : ℝ)] ![(10939261048971/25000000000000 : ℝ), (13715398660061/100000000000000 : ℝ), (42527557120803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338050989/2500000000 : ℝ)|^8403 ≤ (10939261048971/25000000000000 : ℝ)^6355
        have hw : |(1338050989/2500000000 : ℝ)|=(1338050989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2225820487/10000000000 : ℝ)|^8403 ≤ (13715398660061/100000000000000 : ℝ)^6355
        have hw : |(-2225820487/10000000000 : ℝ)|=(2225820487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130951901/250000000 : ℝ)|^8403 ≤ (42527557120803/100000000000000 : ℝ)^6355
        have hw : |(130951901/250000000 : ℝ)|=(130951901/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s3_2 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352203863/10000000000 : ℝ)*x 0 + (40922471/78125000 : ℝ)*x 1 + (-556455071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352203863/10000000000 : ℝ)^8403 ≤ (21878521595267/50000000000000 : ℝ)^6355 := by
    have hnat : (5352203863 : ℕ)^8403*50000000000000^6355 ≤ 21878521595267^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352203863 10000000000 21878521595267 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40922471/78125000 : ℝ)^8403 ≤ (42527559783177/100000000000000 : ℝ)^6355 := by
    have hnat : (40922471 : ℕ)^8403*100000000000000^6355 ≤ 42527559783177^6355*78125000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40922471 78125000 42527559783177 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (556455071/2500000000 : ℝ)^8403 ≤ (1371539700607/10000000000000 : ℝ)^6355 := by
    have hnat : (556455071 : ℕ)^8403*10000000000000^6355 ≤ 1371539700607^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556455071 2500000000 1371539700607 10000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352203863/10000000000 : ℝ), (40922471/78125000 : ℝ), (-556455071/2500000000 : ℝ)] ![(21878521595267/50000000000000 : ℝ), (42527559783177/100000000000000 : ℝ), (1371539700607/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352203863/10000000000 : ℝ)|^8403 ≤ (21878521595267/50000000000000 : ℝ)^6355
        have hw : |(5352203863/10000000000 : ℝ)|=(5352203863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40922471/78125000 : ℝ)|^8403 ≤ (42527559783177/100000000000000 : ℝ)^6355
        have hw : |(40922471/78125000 : ℝ)|=(40922471/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-556455071/2500000000 : ℝ)|^8403 ≤ (1371539700607/10000000000000 : ℝ)^6355
        have hw : |(-556455071/2500000000 : ℝ)|=(556455071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s3_3 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088330061/2500000000 : ℝ)*x 0 + (2085634421/5000000000 : ℝ)*x 1 + (227157073/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088330061/2500000000 : ℝ)^8403 ≤ (16649255189291/50000000000000 : ℝ)^6355 := by
    have hnat : (1088330061 : ℕ)^8403*50000000000000^6355 ≤ 16649255189291^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088330061 2500000000 16649255189291 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085634421/5000000000 : ℝ)^8403 ≤ (7867442210533/25000000000000 : ℝ)^6355 := by
    have hnat : (2085634421 : ℕ)^8403*25000000000000^6355 ≤ 7867442210533^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085634421 5000000000 7867442210533 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227157073/500000000 : ℝ)^8403 ≤ (7046344153087/20000000000000 : ℝ)^6355 := by
    have hnat : (227157073 : ℕ)^8403*20000000000000^6355 ≤ 7046344153087^6355*500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227157073 500000000 7046344153087 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088330061/2500000000 : ℝ), (2085634421/5000000000 : ℝ), (227157073/500000000 : ℝ)] ![(16649255189291/50000000000000 : ℝ), (7867442210533/25000000000000 : ℝ), (7046344153087/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088330061/2500000000 : ℝ)|^8403 ≤ (16649255189291/50000000000000 : ℝ)^6355
        have hw : |(1088330061/2500000000 : ℝ)|=(1088330061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085634421/5000000000 : ℝ)|^8403 ≤ (7867442210533/25000000000000 : ℝ)^6355
        have hw : |(2085634421/5000000000 : ℝ)|=(2085634421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(227157073/500000000 : ℝ)|^8403 ≤ (7046344153087/20000000000000 : ℝ)^6355
        have hw : |(227157073/500000000 : ℝ)|=(227157073/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s3_4 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-532920129/2500000000 : ℝ)*x 0 + (5238760077/10000000000 : ℝ)*x 1 + (216873793/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532920129/2500000000 : ℝ)^8403 ≤ (12953648924199/100000000000000 : ℝ)^6355 := by
    have hnat : (532920129 : ℕ)^8403*100000000000000^6355 ≤ 12953648924199^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532920129 2500000000 12953648924199 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238760077/10000000000 : ℝ)^8403 ≤ (10633725168217/25000000000000 : ℝ)^6355 := by
    have hnat : (5238760077 : ℕ)^8403*25000000000000^6355 ≤ 10633725168217^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238760077 10000000000 10633725168217 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216873793/400000000 : ℝ)^8403 ≤ (5563931298881/12500000000000 : ℝ)^6355 := by
    have hnat : (216873793 : ℕ)^8403*12500000000000^6355 ≤ 5563931298881^6355*400000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216873793 400000000 5563931298881 12500000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-532920129/2500000000 : ℝ), (5238760077/10000000000 : ℝ), (216873793/400000000 : ℝ)] ![(12953648924199/100000000000000 : ℝ), (10633725168217/25000000000000 : ℝ), (5563931298881/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-532920129/2500000000 : ℝ)|^8403 ≤ (12953648924199/100000000000000 : ℝ)^6355
        have hw : |(-532920129/2500000000 : ℝ)|=(532920129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238760077/10000000000 : ℝ)|^8403 ≤ (10633725168217/25000000000000 : ℝ)^6355
        have hw : |(5238760077/10000000000 : ℝ)|=(5238760077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216873793/400000000 : ℝ)|^8403 ≤ (5563931298881/12500000000000 : ℝ)^6355
        have hw : |(216873793/400000000 : ℝ)|=(216873793/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s3_5 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305246453/10000000000 : ℝ)*x 0 + (-2042051859/10000000000 : ℝ)*x 1 + (338865317/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305246453/10000000000 : ℝ)^8403 ≤ (21625071388101/50000000000000 : ℝ)^6355 := by
    have hnat : (5305246453 : ℕ)^8403*50000000000000^6355 ≤ 21625071388101^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305246453 10000000000 21625071388101 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2042051859/10000000000 : ℝ)^8403 ≤ (122384041391/1000000000000 : ℝ)^6355 := by
    have hnat : (2042051859 : ℕ)^8403*1000000000000^6355 ≤ 122384041391^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042051859 10000000000 122384041391 1000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338865317/625000000 : ℝ)^8403 ≤ (44511453072317/100000000000000 : ℝ)^6355 := by
    have hnat : (338865317 : ℕ)^8403*100000000000000^6355 ≤ 44511453072317^6355*625000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338865317 625000000 44511453072317 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305246453/10000000000 : ℝ), (-2042051859/10000000000 : ℝ), (338865317/625000000 : ℝ)] ![(21625071388101/50000000000000 : ℝ), (122384041391/1000000000000 : ℝ), (44511453072317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305246453/10000000000 : ℝ)|^8403 ≤ (21625071388101/50000000000000 : ℝ)^6355
        have hw : |(5305246453/10000000000 : ℝ)|=(5305246453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2042051859/10000000000 : ℝ)|^8403 ≤ (122384041391/1000000000000 : ℝ)^6355
        have hw : |(-2042051859/10000000000 : ℝ)|=(2042051859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338865317/625000000 : ℝ)|^8403 ≤ (44511453072317/100000000000000 : ℝ)^6355
        have hw : |(338865317/625000000 : ℝ)|=(338865317/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s3_6 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (42441981/80000000 : ℝ)*x 0 + (135546113/250000000 : ℝ)*x 1 + (-102102551/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42441981/80000000 : ℝ)^8403 ≤ (43250155409839/100000000000000 : ℝ)^6355 := by
    have hnat : (42441981 : ℕ)^8403*100000000000000^6355 ≤ 43250155409839^6355*80000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42441981 80000000 43250155409839 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135546113/250000000 : ℝ)^8403 ≤ (44511447080169/100000000000000 : ℝ)^6355 := by
    have hnat : (135546113 : ℕ)^8403*100000000000000^6355 ≤ 44511447080169^6355*250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135546113 250000000 44511447080169 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102102551/500000000 : ℝ)^8403 ≤ (12238397490369/100000000000000 : ℝ)^6355 := by
    have hnat : (102102551 : ℕ)^8403*100000000000000^6355 ≤ 12238397490369^6355*500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102102551 500000000 12238397490369 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42441981/80000000 : ℝ), (135546113/250000000 : ℝ), (-102102551/500000000 : ℝ)] ![(43250155409839/100000000000000 : ℝ), (44511447080169/100000000000000 : ℝ), (12238397490369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42441981/80000000 : ℝ)|^8403 ≤ (43250155409839/100000000000000 : ℝ)^6355
        have hw : |(42441981/80000000 : ℝ)|=(42441981/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135546113/250000000 : ℝ)|^8403 ≤ (44511447080169/100000000000000 : ℝ)^6355
        have hw : |(135546113/250000000 : ℝ)|=(135546113/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-102102551/500000000 : ℝ)|^8403 ≤ (12238397490369/100000000000000 : ℝ)^6355
        have hw : |(-102102551/500000000 : ℝ)|=(102102551/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s3_7 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2176675519/5000000000 : ℝ)*x 0 + (454176281/1000000000 : ℝ)*x 1 + (4172654597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176675519/5000000000 : ℝ)^8403 ≤ (2081176364343/6250000000000 : ℝ)^6355 := by
    have hnat : (2176675519 : ℕ)^8403*6250000000000^6355 ≤ 2081176364343^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176675519 5000000000 2081176364343 6250000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454176281/1000000000 : ℝ)^8403 ≤ (3521758467901/10000000000000 : ℝ)^6355 := by
    have hnat : (454176281 : ℕ)^8403*10000000000000^6355 ≤ 3521758467901^6355*1000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454176281 1000000000 3521758467901 10000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172654597/10000000000 : ℝ)^8403 ≤ (31483593483697/100000000000000 : ℝ)^6355 := by
    have hnat : (4172654597 : ℕ)^8403*100000000000000^6355 ≤ 31483593483697^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172654597 10000000000 31483593483697 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176675519/5000000000 : ℝ), (454176281/1000000000 : ℝ), (4172654597/10000000000 : ℝ)] ![(2081176364343/6250000000000 : ℝ), (3521758467901/10000000000000 : ℝ), (31483593483697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176675519/5000000000 : ℝ)|^8403 ≤ (2081176364343/6250000000000 : ℝ)^6355
        have hw : |(2176675519/5000000000 : ℝ)|=(2176675519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(454176281/1000000000 : ℝ)|^8403 ≤ (3521758467901/10000000000000 : ℝ)^6355
        have hw : |(454176281/1000000000 : ℝ)|=(454176281/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172654597/10000000000 : ℝ)|^8403 ≤ (31483593483697/100000000000000 : ℝ)^6355
        have hw : |(4172654597/10000000000 : ℝ)|=(4172654597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1210_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10827/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14731/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4077/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4077/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4077/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4077/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4077/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4077/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9367/100000 : ℝ) ^ (4201/1024 : ℝ) ≤ (603880439410507/10000000000000000000 : ℝ) := by
    have hpowers : (9367/100000 : ℝ)^4201 ≤ (603880439410507/10000000000000000000 : ℝ)^1024 := by
      have hnat : (9367 : ℕ)^4201*10000000000000000000^1024 ≤ 603880439410507^1024*100000^4201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9367 100000 603880439410507 10000000000000000000 4201 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9367/100000 : ℝ)) (X := (603880439410507/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4077/25000 : ℝ) ^ (4201/1024 : ℝ) ≤ (14681929225963007/25000000000000000000 : ℝ) := by
    have hpowers : (4077/25000 : ℝ)^4201 ≤ (14681929225963007/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4077 : ℕ)^4201*25000000000000000000^1024 ≤ 14681929225963007^1024*25000^4201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4077 25000 14681929225963007 25000000000000000000 4201 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4077/25000 : ℝ)) (X := (14681929225963007/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000603880439410507/5000000000000000000 : ℝ) ≤ (1250036797508441/1250000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (5000603880439410507/5000000000000000000 : ℝ)^1024 ≤ (1250036797508441/1250000000000000 : ℝ)^4201 := by
      have hnat : (5000603880439410507 : ℕ)^1024*1250000000000000^4201 ≤ 1250036797508441^4201*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000603880439410507 5000000000000000000 1250036797508441 1250000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250036797508441/1250000000000000 : ℝ)) (X := (5000603880439410507/5000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50032383260648978549/50000000000000000000 : ℝ) ≤ (5000789153559977/5000000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (50032383260648978549/50000000000000000000 : ℝ)^1024 ≤ (5000789153559977/5000000000000000 : ℝ)^4201 := by
      have hnat : (50032383260648978549 : ℕ)^1024*5000000000000000^4201 ≤ 5000789153559977^4201*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032383260648978549 50000000000000000000 5000789153559977 5000000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000789153559977/5000000000000000 : ℝ)) (X := (50032383260648978549/50000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12514681929225963007/12500000000000000000 : ℝ) ≤ (500143111708619/500000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (12514681929225963007/12500000000000000000 : ℝ)^1024 ≤ (500143111708619/500000000000000 : ℝ)^4201 := by
      have hnat : (12514681929225963007 : ℕ)^1024*500000000000000^4201 ≤ 500143111708619^4201*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12514681929225963007 12500000000000000000 500143111708619 500000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500143111708619/500000000000000 : ℝ)) (X := (12514681929225963007/12500000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(603880439410507/10000000000000000000 : ℝ) ≤ ((17346997550662140791/17352500000000000000 : ℝ)+2*(641963526213/347050000000000 : ℝ)*(9367/100000 : ℝ))^(4201/1024 : ℝ) := by
    rw [show (17346997550662140791/17352500000000000000 : ℝ)+2*(641963526213/347050000000000 : ℝ)*(9367/100000 : ℝ)=(1250036797508441/1250000000000000 : ℝ) by norm_num, show 1+2*(603880439410507/10000000000000000000 : ℝ)=(5000603880439410507/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14681929225963007/25000000000000000000 : ℝ)+(603880439410507/10000000000000000000 : ℝ) ≤ ((17346997550662140791/17352500000000000000 : ℝ)+(641963526213/347050000000000 : ℝ)*((4077/25000 : ℝ)+(9367/100000 : ℝ)))^(4201/1024 : ℝ) := by
    rw [show (17346997550662140791/17352500000000000000 : ℝ)+(641963526213/347050000000000 : ℝ)*((4077/25000 : ℝ)+(9367/100000 : ℝ))=(5000789153559977/5000000000000000 : ℝ) by norm_num, show 1+(14681929225963007/25000000000000000000 : ℝ)+(603880439410507/10000000000000000000 : ℝ)=(50032383260648978549/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14681929225963007/25000000000000000000 : ℝ) ≤ ((17346997550662140791/17352500000000000000 : ℝ)+2*(641963526213/347050000000000 : ℝ)*(4077/25000 : ℝ))^(4201/1024 : ℝ) := by
    rw [show (17346997550662140791/17352500000000000000 : ℝ)+2*(641963526213/347050000000000 : ℝ)*(4077/25000 : ℝ)=(500143111708619/500000000000000 : ℝ) by norm_num, show 1+2*(14681929225963007/25000000000000000000 : ℝ)=(12514681929225963007/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17346997550662140791/17352500000000000000 : ℝ)*(X 1 0+X 2 0)+(641963526213/347050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (9367/100000 : ℝ)) (hi := (4077/25000 : ℝ)) (c := (17346997550662140791/17352500000000000000 : ℝ)) (alpha := (641963526213/347050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17346997550662140791/17352500000000000000 : ℝ)*(X 0 1+X 2 1)+(641963526213/347050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (9367/100000 : ℝ)) (hi := (4077/25000 : ℝ)) (c := (17346997550662140791/17352500000000000000 : ℝ)) (alpha := (641963526213/347050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17346997550662140791/17352500000000000000 : ℝ)*(X 0 2+X 1 2)+(641963526213/347050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (9367/100000 : ℝ)) (hi := (4077/25000 : ℝ)) (c := (17346997550662140791/17352500000000000000 : ℝ)) (alpha := (641963526213/347050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-213166511/1000000000 : ℝ)*X 0 0+(1355633211/2500000000 : ℝ)*X 0 1+(5238075901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338050989/2500000000 : ℝ)*X 1 0+(-2225820487/10000000000 : ℝ)*X 1 1+(130951901/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352203863/10000000000 : ℝ)*X 2 0+(40922471/78125000 : ℝ)*X 2 1+(-556455071/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088330061/2500000000 : ℝ)*X 0 0+(2085634421/5000000000 : ℝ)*X 0 1+(227157073/500000000 : ℝ)*X 0 2+(1088330061/2500000000 : ℝ)*X 1 0+(2085634421/5000000000 : ℝ)*X 1 1+(227157073/500000000 : ℝ)*X 1 2+(1088330061/2500000000 : ℝ)*X 2 0+(2085634421/5000000000 : ℝ)*X 2 1+(227157073/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-532920129/2500000000 : ℝ)*X 0 0+(5238760077/10000000000 : ℝ)*X 0 1+(216873793/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305246453/10000000000 : ℝ)*X 1 0+(-2042051859/10000000000 : ℝ)*X 1 1+(338865317/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((42441981/80000000 : ℝ)*X 2 0+(135546113/250000000 : ℝ)*X 2 1+(-102102551/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176675519/5000000000 : ℝ)*X 0 0+(454176281/1000000000 : ℝ)*X 0 1+(4172654597/10000000000 : ℝ)*X 0 2+(2176675519/5000000000 : ℝ)*X 1 0+(454176281/1000000000 : ℝ)*X 1 1+(4172654597/10000000000 : ℝ)*X 1 2+(2176675519/5000000000 : ℝ)*X 2 0+(454176281/1000000000 : ℝ)*X 2 1+(4172654597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (360394528486997936827841721/39437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (186474003/12500000000000 : ℝ)*(base19) + (1198792011/100000000000000 : ℝ)*(base23) + (3325021/3125000000000 : ℝ)*(lower2) + (107061041/100000000000000 : ℝ)*(upper3) + (10405099/6250000000000 : ℝ)*(upper5) + (2027628210402949/50000000000000 : ℝ)*(major0) + (2027628210402949/50000000000000 : ℝ)*(major1) + (2027628210402949/50000000000000 : ℝ)*(major2) + (169417266891437/3125000000000 : ℝ)*(sp0) + (5421387979694629/100000000000000 : ℝ)*(sp1) + (2710694136347321/50000000000000 : ℝ)*(sp2) + (672277025165559/25000000000000 : ℝ)*(sp3) + (3693096067/10000000000000 : ℝ)*(sp4) + (14964850513/100000000000000 : ℝ)*(sp7) + (672280766378187/25000000000000 : ℝ)*(f.failure) + (5421389471486653/100000000000000 : ℝ)*(f.sum) + (3423634941211/1577500000000000000000000000 : ℝ)*base66 + (525635184467687031/78875000000000000000000000000000 : ℝ)*base68 + (732827570197312031/78875000000000000000000000000000 : ℝ)*base70 + (446790005054437031/78875000000000000000000000000000 : ℝ)*base72 + (3653286074577/3155000000000000000000000000 : ℝ)*base74 + (662537705848062031/78875000000000000000000000000000 : ℝ)*base76 + (393632176877187031/78875000000000000000000000000000 : ℝ)*base78 + (493790098106437031/78875000000000000000000000000000 : ℝ)*base80 + (4599270465547/3155000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (3731711/625000000000000000000 : ℝ)*base90 + (3731711/625000000000000000000 : ℝ)*base92 + (3731711/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (262913204645369532047991837/78875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2543759/400000000000 : ℝ)*(base19) + (218964071/10000000000000 : ℝ)*(base23) + (6370627/100000000000000 : ℝ)*(upper2) + (123738927/50000000000000 : ℝ)*(upper3) + (4085598611542459/100000000000000 : ℝ)*(major0) + (4085598611542459/100000000000000 : ℝ)*(major1) + (4085598611542459/100000000000000 : ℝ)*(major2) + (4858693157/50000000000000 : ℝ)*(sp1) + (47575307943/100000000000000 : ℝ)*(sp2) + (531064309/50000000000000 : ℝ)*(sp3) + (341372095141163/6250000000000 : ℝ)*(sp4) + (1092388633786509/20000000000000 : ℝ)*(sp5) + (1092380751461991/20000000000000 : ℝ)*(sp6) + (2709242527588037/100000000000000 : ℝ)*(sp7) + (169327724357291/6250000000000 : ℝ)*(f.failure) + (341372095141163/6250000000000 : ℝ)*(f.sum) + (116720747609/197187500000000000000000000 : ℝ)*base65 + (294474342839527721/157750000000000000000000000000000 : ℝ)*base68 + (96095014298777721/157750000000000000000000000000000 : ℝ)*base70 + (437891212691722279/157750000000000000000000000000000 : ℝ)*base71 + (3039643928621/3155000000000000000000000000 : ℝ)*base74 + (1563088173598777721/157750000000000000000000000000000 : ℝ)*base76 + (376606681574527721/157750000000000000000000000000000 : ℝ)*base78 + (727026416858472279/157750000000000000000000000000000 : ℝ)*base79 + (11129523527759/3155000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1950677/156250000000000000000 : ℝ)*base89 + (1950677/156250000000000000000 : ℝ)*base91 + (1950677/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1210_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10827/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1210_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1210_s4_0 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134164051/10000000000 : ℝ)*x 0 + (5398819273/10000000000 : ℝ)*x 1 + (657519103/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134164051/10000000000 : ℝ)^8403 ≤ (3243402001993/25000000000000 : ℝ)^6355 := by
    have hnat : (2134164051 : ℕ)^8403*25000000000000^6355 ≤ 3243402001993^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134164051 10000000000 3243402001993 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398819273/10000000000 : ℝ)^8403 ≤ (22130835688957/50000000000000 : ℝ)^6355 := by
    have hnat : (5398819273 : ℕ)^8403*50000000000000^6355 ≤ 22130835688957^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398819273 10000000000 22130835688957 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657519103/1250000000 : ℝ)^8403 ≤ (42764720600721/100000000000000 : ℝ)^6355 := by
    have hnat : (657519103 : ℕ)^8403*100000000000000^6355 ≤ 42764720600721^6355*1250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657519103 1250000000 42764720600721 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134164051/10000000000 : ℝ), (5398819273/10000000000 : ℝ), (657519103/1250000000 : ℝ)] ![(3243402001993/25000000000000 : ℝ), (22130835688957/50000000000000 : ℝ), (42764720600721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134164051/10000000000 : ℝ)|^8403 ≤ (3243402001993/25000000000000 : ℝ)^6355
        have hw : |(-2134164051/10000000000 : ℝ)|=(2134164051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398819273/10000000000 : ℝ)|^8403 ≤ (22130835688957/50000000000000 : ℝ)^6355
        have hw : |(5398819273/10000000000 : ℝ)|=(5398819273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657519103/1250000000 : ℝ)|^8403 ≤ (42764720600721/100000000000000 : ℝ)^6355
        have hw : |(657519103/1250000000 : ℝ)|=(657519103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s4_1 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346243343/10000000000 : ℝ)*x 0 + (-275573351/1250000000 : ℝ)*x 1 + (5260152861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346243343/10000000000 : ℝ)^8403 ≤ (8738524056667/20000000000000 : ℝ)^6355 := by
    have hnat : (5346243343 : ℕ)^8403*20000000000000^6355 ≤ 8738524056667^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346243343 10000000000 8738524056667 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275573351/1250000000 : ℝ)^8403 ≤ (846416168739/6250000000000 : ℝ)^6355 := by
    have hnat : (275573351 : ℕ)^8403*6250000000000^6355 ≤ 846416168739^6355*1250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275573351 1250000000 846416168739 6250000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260152861/10000000000 : ℝ)^8403 ≤ (10691180249617/25000000000000 : ℝ)^6355 := by
    have hnat : (5260152861 : ℕ)^8403*25000000000000^6355 ≤ 10691180249617^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260152861 10000000000 10691180249617 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346243343/10000000000 : ℝ), (-275573351/1250000000 : ℝ), (5260152861/10000000000 : ℝ)] ![(8738524056667/20000000000000 : ℝ), (846416168739/6250000000000 : ℝ), (10691180249617/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346243343/10000000000 : ℝ)|^8403 ≤ (8738524056667/20000000000000 : ℝ)^6355
        have hw : |(5346243343/10000000000 : ℝ)|=(5346243343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-275573351/1250000000 : ℝ)|^8403 ≤ (846416168739/6250000000000 : ℝ)^6355
        have hw : |(-275573351/1250000000 : ℝ)|=(275573351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260152861/10000000000 : ℝ)|^8403 ≤ (10691180249617/25000000000000 : ℝ)^6355
        have hw : |(5260152861/10000000000 : ℝ)|=(5260152861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s4_2 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346243389/10000000000 : ℝ)*x 0 + (5260152861/10000000000 : ℝ)*x 1 + (-2204586747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346243389/10000000000 : ℝ)^8403 ≤ (21846310390213/50000000000000 : ℝ)^6355 := by
    have hnat : (5346243389 : ℕ)^8403*50000000000000^6355 ≤ 21846310390213^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346243389 10000000000 21846310390213 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260152861/10000000000 : ℝ)^8403 ≤ (10691180249617/25000000000000 : ℝ)^6355 := by
    have hnat : (5260152861 : ℕ)^8403*25000000000000^6355 ≤ 10691180249617^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260152861 10000000000 10691180249617 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2204586747/10000000000 : ℝ)^8403 ≤ (2708531640869/20000000000000 : ℝ)^6355 := by
    have hnat : (2204586747 : ℕ)^8403*20000000000000^6355 ≤ 2708531640869^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204586747 10000000000 2708531640869 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346243389/10000000000 : ℝ), (5260152861/10000000000 : ℝ), (-2204586747/10000000000 : ℝ)] ![(21846310390213/50000000000000 : ℝ), (10691180249617/25000000000000 : ℝ), (2708531640869/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346243389/10000000000 : ℝ)|^8403 ≤ (21846310390213/50000000000000 : ℝ)^6355
        have hw : |(5346243389/10000000000 : ℝ)|=(5346243389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260152861/10000000000 : ℝ)|^8403 ≤ (10691180249617/25000000000000 : ℝ)^6355
        have hw : |(5260152861/10000000000 : ℝ)|=(5260152861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2204586747/10000000000 : ℝ)|^8403 ≤ (2708531640869/20000000000000 : ℝ)^6355
        have hw : |(-2204586747/10000000000 : ℝ)|=(2204586747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s4_3 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (544352081/1250000000 : ℝ)*x 0 + (4217234529/10000000000 : ℝ)*x 1 + (2248395963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544352081/1250000000 : ℝ)^8403 ≤ (4164205731067/12500000000000 : ℝ)^6355 := by
    have hnat : (544352081 : ℕ)^8403*12500000000000^6355 ≤ 4164205731067^6355*1250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544352081 1250000000 4164205731067 12500000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4217234529/10000000000 : ℝ)^8403 ≤ (31929121767047/100000000000000 : ℝ)^6355 := by
    have hnat : (4217234529 : ℕ)^8403*100000000000000^6355 ≤ 31929121767047^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217234529 10000000000 31929121767047 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248395963/5000000000 : ℝ)^8403 ≤ (34757232364937/100000000000000 : ℝ)^6355 := by
    have hnat : (2248395963 : ℕ)^8403*100000000000000^6355 ≤ 34757232364937^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248395963 5000000000 34757232364937 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544352081/1250000000 : ℝ), (4217234529/10000000000 : ℝ), (2248395963/5000000000 : ℝ)] ![(4164205731067/12500000000000 : ℝ), (31929121767047/100000000000000 : ℝ), (34757232364937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544352081/1250000000 : ℝ)|^8403 ≤ (4164205731067/12500000000000 : ℝ)^6355
        have hw : |(544352081/1250000000 : ℝ)|=(544352081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4217234529/10000000000 : ℝ)|^8403 ≤ (31929121767047/100000000000000 : ℝ)^6355
        have hw : |(4217234529/10000000000 : ℝ)|=(4217234529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248395963/5000000000 : ℝ)|^8403 ≤ (34757232364937/100000000000000 : ℝ)^6355
        have hw : |(2248395963/5000000000 : ℝ)|=(2248395963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s4_4 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134170493/10000000000 : ℝ)*x 0 + (32878373/62500000 : ℝ)*x 1 + (2699215431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134170493/10000000000 : ℝ)^8403 ≤ (3243414947311/25000000000000 : ℝ)^6355 := by
    have hnat : (2134170493 : ℕ)^8403*25000000000000^6355 ≤ 3243414947311^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134170493 10000000000 3243414947311 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32878373/62500000 : ℝ)^8403 ≤ (1710755173169/4000000000000 : ℝ)^6355 := by
    have hnat : (32878373 : ℕ)^8403*4000000000000^6355 ≤ 1710755173169^6355*62500000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32878373 62500000 1710755173169 4000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699215431/5000000000 : ℝ)^8403 ≤ (17288070653/39062500000 : ℝ)^6355 := by
    have hnat : (2699215431 : ℕ)^8403*39062500000^6355 ≤ 17288070653^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699215431 5000000000 17288070653 39062500000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134170493/10000000000 : ℝ), (32878373/62500000 : ℝ), (2699215431/5000000000 : ℝ)] ![(3243414947311/25000000000000 : ℝ), (1710755173169/4000000000000 : ℝ), (17288070653/39062500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134170493/10000000000 : ℝ)|^8403 ≤ (3243414947311/25000000000000 : ℝ)^6355
        have hw : |(-2134170493/10000000000 : ℝ)|=(2134170493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32878373/62500000 : ℝ)|^8403 ≤ (1710755173169/4000000000000 : ℝ)^6355
        have hw : |(32878373/62500000 : ℝ)|=(32878373/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699215431/5000000000 : ℝ)|^8403 ≤ (17288070653/39062500000 : ℝ)^6355
        have hw : |(2699215431/5000000000 : ℝ)|=(2699215431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s4_5 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655470449/5000000000 : ℝ)*x 0 + (-206630989/1000000000 : ℝ)*x 1 + (2699215249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655470449/5000000000 : ℝ)^8403 ≤ (43311536967251/100000000000000 : ℝ)^6355 := by
    have hnat : (2655470449 : ℕ)^8403*100000000000000^6355 ≤ 43311536967251^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655470449 5000000000 43311536967251 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206630989/1000000000 : ℝ)^8403 ≤ (12431006083857/100000000000000 : ℝ)^6355 := by
    have hnat : (206630989 : ℕ)^8403*100000000000000^6355 ≤ 12431006083857^6355*1000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206630989 1000000000 12431006083857 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699215249/5000000000 : ℝ)^8403 ≤ (44257456925843/100000000000000 : ℝ)^6355 := by
    have hnat : (2699215249 : ℕ)^8403*100000000000000^6355 ≤ 44257456925843^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699215249 5000000000 44257456925843 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655470449/5000000000 : ℝ), (-206630989/1000000000 : ℝ), (2699215249/5000000000 : ℝ)] ![(43311536967251/100000000000000 : ℝ), (12431006083857/100000000000000 : ℝ), (44257456925843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655470449/5000000000 : ℝ)|^8403 ≤ (43311536967251/100000000000000 : ℝ)^6355
        have hw : |(2655470449/5000000000 : ℝ)|=(2655470449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-206630989/1000000000 : ℝ)|^8403 ≤ (12431006083857/100000000000000 : ℝ)^6355
        have hw : |(-206630989/1000000000 : ℝ)|=(206630989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699215249/5000000000 : ℝ)|^8403 ≤ (44257456925843/100000000000000 : ℝ)^6355
        have hw : |(2699215249/5000000000 : ℝ)|=(2699215249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s4_6 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (10372933/19531250 : ℝ)*x 0 + (2699215051/5000000000 : ℝ)*x 1 + (-516577337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10372933/19531250 : ℝ)^8403 ≤ (4331154557231/10000000000000 : ℝ)^6355 := by
    have hnat : (10372933 : ℕ)^8403*10000000000000^6355 ≤ 4331154557231^6355*19531250^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10372933 19531250 4331154557231 10000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699215051/5000000000 : ℝ)^8403 ≤ (44257452633119/100000000000000 : ℝ)^6355 := by
    have hnat : (2699215051 : ℕ)^8403*100000000000000^6355 ≤ 44257452633119^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699215051 5000000000 44257452633119 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516577337/2500000000 : ℝ)^8403 ≤ (194234402693/1562500000000 : ℝ)^6355 := by
    have hnat : (516577337 : ℕ)^8403*1562500000000^6355 ≤ 194234402693^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516577337 2500000000 194234402693 1562500000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10372933/19531250 : ℝ), (2699215051/5000000000 : ℝ), (-516577337/2500000000 : ℝ)] ![(4331154557231/10000000000000 : ℝ), (44257452633119/100000000000000 : ℝ), (194234402693/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10372933/19531250 : ℝ)|^8403 ≤ (4331154557231/10000000000000 : ℝ)^6355
        have hw : |(10372933/19531250 : ℝ)|=(10372933/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699215051/5000000000 : ℝ)|^8403 ≤ (44257452633119/100000000000000 : ℝ)^6355
        have hw : |(2699215051/5000000000 : ℝ)|=(2699215051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-516577337/2500000000 : ℝ)|^8403 ≤ (194234402693/1562500000000 : ℝ)^6355
        have hw : |(-516577337/2500000000 : ℝ)|=(516577337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s4_7 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4354830279/10000000000 : ℝ)*x 0 + (899202263/2000000000 : ℝ)*x 1 + (4218017637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354830279/10000000000 : ℝ)^8403 ≤ (1332551349113/4000000000000 : ℝ)^6355 := by
    have hnat : (4354830279 : ℕ)^8403*4000000000000^6355 ≤ 1332551349113^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354830279 10000000000 1332551349113 4000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899202263/2000000000 : ℝ)^8403 ≤ (34749254554333/100000000000000 : ℝ)^6355 := by
    have hnat : (899202263 : ℕ)^8403*100000000000000^6355 ≤ 34749254554333^6355*2000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899202263 2000000000 34749254554333 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4218017637/10000000000 : ℝ)^8403 ≤ (7984240426507/25000000000000 : ℝ)^6355 := by
    have hnat : (4218017637 : ℕ)^8403*25000000000000^6355 ≤ 7984240426507^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218017637 10000000000 7984240426507 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354830279/10000000000 : ℝ), (899202263/2000000000 : ℝ), (4218017637/10000000000 : ℝ)] ![(1332551349113/4000000000000 : ℝ), (34749254554333/100000000000000 : ℝ), (7984240426507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354830279/10000000000 : ℝ)|^8403 ≤ (1332551349113/4000000000000 : ℝ)^6355
        have hw : |(4354830279/10000000000 : ℝ)|=(4354830279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899202263/2000000000 : ℝ)|^8403 ≤ (34749254554333/100000000000000 : ℝ)^6355
        have hw : |(899202263/2000000000 : ℝ)|=(899202263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4218017637/10000000000 : ℝ)|^8403 ≤ (7984240426507/25000000000000 : ℝ)^6355
        have hw : |(4218017637/10000000000 : ℝ)|=(4218017637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1210_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10827/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5649/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10827/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10827/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10827/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10827/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10827/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10827/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10827/100000 : ℝ) ^ (4201/1024 : ℝ) ≤ (2735091912146111/25000000000000000000 : ℝ) := by
    have hpowers : (10827/100000 : ℝ)^4201 ≤ (2735091912146111/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10827 : ℕ)^4201*25000000000000000000^1024 ≤ 2735091912146111^1024*100000^4201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10827 100000 2735091912146111 25000000000000000000 4201 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10827/100000 : ℝ)) (X := (2735091912146111/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14731/100000 : ℝ) ^ (4201/1024 : ℝ) ≤ (38693697370636709/100000000000000000000 : ℝ) := by
    have hpowers : (14731/100000 : ℝ)^4201 ≤ (38693697370636709/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14731 : ℕ)^4201*100000000000000000000^1024 ≤ 38693697370636709^1024*100000^4201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14731 100000 38693697370636709 100000000000000000000 4201 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14731/100000 : ℝ)) (X := (38693697370636709/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502735091912146111/12500000000000000000 : ℝ) ≤ (5000266651028341/5000000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (12502735091912146111/12500000000000000000 : ℝ)^1024 ≤ (5000266651028341/5000000000000000 : ℝ)^4201 := by
      have hnat : (12502735091912146111 : ℕ)^1024*5000000000000000^4201 ≤ 5000266651028341^4201*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502735091912146111 12500000000000000000 5000266651028341 5000000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000266651028341/5000000000000000 : ℝ)) (X := (12502735091912146111/12500000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049634065019221153/100000000000000000000 : ℝ) ≤ (5000604805362303/5000000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (100049634065019221153/100000000000000000000 : ℝ)^1024 ≤ (5000604805362303/5000000000000000 : ℝ)^4201 := by
      have hnat : (100049634065019221153 : ℕ)^1024*5000000000000000^4201 ≤ 5000604805362303^4201*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049634065019221153 100000000000000000000 5000604805362303 5000000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000604805362303/5000000000000000 : ℝ)) (X := (100049634065019221153/100000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038693697370636709/50000000000000000000 : ℝ) ≤ (1000188591939253/1000000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (50038693697370636709/50000000000000000000 : ℝ)^1024 ≤ (1000188591939253/1000000000000000 : ℝ)^4201 := by
      have hnat : (50038693697370636709 : ℕ)^1024*1000000000000000^4201 ≤ 1000188591939253^4201*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038693697370636709 50000000000000000000 1000188591939253 1000000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000188591939253/1000000000000000 : ℝ)) (X := (50038693697370636709/50000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2735091912146111/25000000000000000000 : ℝ) ≤ ((4878429652916757529/4880000000000000000 : ℝ)+2*(169077166981/97600000000000 : ℝ)*(10827/100000 : ℝ))^(4201/1024 : ℝ) := by
    rw [show (4878429652916757529/4880000000000000000 : ℝ)+2*(169077166981/97600000000000 : ℝ)*(10827/100000 : ℝ)=(5000266651028341/5000000000000000 : ℝ) by norm_num, show 1+2*(2735091912146111/25000000000000000000 : ℝ)=(12502735091912146111/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38693697370636709/100000000000000000000 : ℝ)+(2735091912146111/25000000000000000000 : ℝ) ≤ ((4878429652916757529/4880000000000000000 : ℝ)+(169077166981/97600000000000 : ℝ)*((14731/100000 : ℝ)+(10827/100000 : ℝ)))^(4201/1024 : ℝ) := by
    rw [show (4878429652916757529/4880000000000000000 : ℝ)+(169077166981/97600000000000 : ℝ)*((14731/100000 : ℝ)+(10827/100000 : ℝ))=(5000604805362303/5000000000000000 : ℝ) by norm_num, show 1+(38693697370636709/100000000000000000000 : ℝ)+(2735091912146111/25000000000000000000 : ℝ)=(100049634065019221153/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38693697370636709/100000000000000000000 : ℝ) ≤ ((4878429652916757529/4880000000000000000 : ℝ)+2*(169077166981/97600000000000 : ℝ)*(14731/100000 : ℝ))^(4201/1024 : ℝ) := by
    rw [show (4878429652916757529/4880000000000000000 : ℝ)+2*(169077166981/97600000000000 : ℝ)*(14731/100000 : ℝ)=(1000188591939253/1000000000000000 : ℝ) by norm_num, show 1+2*(38693697370636709/100000000000000000000 : ℝ)=(50038693697370636709/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4878429652916757529/4880000000000000000 : ℝ)*(X 1 0+X 2 0)+(169077166981/97600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (10827/100000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (4878429652916757529/4880000000000000000 : ℝ)) (alpha := (169077166981/97600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4878429652916757529/4880000000000000000 : ℝ)*(X 0 1+X 2 1)+(169077166981/97600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (10827/100000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (4878429652916757529/4880000000000000000 : ℝ)) (alpha := (169077166981/97600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4878429652916757529/4880000000000000000 : ℝ)*(X 0 2+X 1 2)+(169077166981/97600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (10827/100000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (4878429652916757529/4880000000000000000 : ℝ)) (alpha := (169077166981/97600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2134164051/10000000000 : ℝ)*X 0 0+(5398819273/10000000000 : ℝ)*X 0 1+(657519103/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346243343/10000000000 : ℝ)*X 1 0+(-275573351/1250000000 : ℝ)*X 1 1+(5260152861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346243389/10000000000 : ℝ)*X 2 0+(5260152861/10000000000 : ℝ)*X 2 1+(-2204586747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544352081/1250000000 : ℝ)*X 0 0+(4217234529/10000000000 : ℝ)*X 0 1+(2248395963/5000000000 : ℝ)*X 0 2+(544352081/1250000000 : ℝ)*X 1 0+(4217234529/10000000000 : ℝ)*X 1 1+(2248395963/5000000000 : ℝ)*X 1 2+(544352081/1250000000 : ℝ)*X 2 0+(4217234529/10000000000 : ℝ)*X 2 1+(2248395963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2134170493/10000000000 : ℝ)*X 0 0+(32878373/62500000 : ℝ)*X 0 1+(2699215431/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655470449/5000000000 : ℝ)*X 1 0+(-206630989/1000000000 : ℝ)*X 1 1+(2699215249/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((10372933/19531250 : ℝ)*X 2 0+(2699215051/5000000000 : ℝ)*X 2 1+(-516577337/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354830279/10000000000 : ℝ)*X 0 0+(899202263/2000000000 : ℝ)*X 0 1+(4218017637/10000000000 : ℝ)*X 0 2+(4354830279/10000000000 : ℝ)*X 1 0+(899202263/2000000000 : ℝ)*X 1 1+(4218017637/10000000000 : ℝ)*X 1 2+(4354830279/10000000000 : ℝ)*X 2 0+(899202263/2000000000 : ℝ)*X 2 1+(4218017637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4769946386992217229039/610000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1663478183/100000000000000 : ℝ)*(base19) + (151727571/10000000000000 : ℝ)*(base23) + (55668473/50000000000000 : ℝ)*(lower2) + (33759711/20000000000000 : ℝ)*(upper3) + (115456913/100000000000000 : ℝ)*(upper5) + (674297993713487/12500000000000 : ℝ)*(major0) + (674297993713487/12500000000000 : ℝ)*(major1) + (674297993713487/12500000000000 : ℝ)*(major2) + (1442319022439093/20000000000000 : ℝ)*(sp0) + (7211640191335363/100000000000000 : ℝ)*(sp1) + (1442328067507567/20000000000000 : ℝ)*(sp2) + (1788551571116867/50000000000000 : ℝ)*(sp3) + (46742618081/100000000000000 : ℝ)*(sp4) + (11320857849/50000000000000 : ℝ)*(sp7) + (447140722993679/12500000000000 : ℝ)*(f.failure) + (3605820927406773/50000000000000 : ℝ)*(f.sum) + (2073907229887/610000000000000000000000000 : ℝ)*base65 + (622500389527556377/61000000000000000000000000000000 : ℝ)*base68 + (437028737298556377/61000000000000000000000000000000 : ℝ)*base70 + (692057878349556377/61000000000000000000000000000000 : ℝ)*base72 + (59337266973/610000000000000000000000000 : ℝ)*base74 + (423951824480443623/61000000000000000000000000000000 : ℝ)*base75 + (28542178984443623/61000000000000000000000000000000 : ℝ)*base77 + (445009070962443623/61000000000000000000000000000000 : ℝ)*base79 + (34058788097/610000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (842413/312500000000000000000 : ℝ)*base89 + (842413/312500000000000000000 : ℝ)*base91 + (842413/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3418983338333572900977/488000000000000000000000000 : ℝ) := by norm_num
    linear_combination (804743473/100000000000000 : ℝ)*(base19) + (290251563/20000000000000 : ℝ)*(base23) + (153719393/50000000000000 : ℝ)*(lower2) + (106330889/100000000000000 : ℝ)*(upper3) + (14978097/50000000000000 : ℝ)*(lower4) + (192148849/50000000000000 : ℝ)*(upper5) + (108493340779681/2000000000000 : ℝ)*(major0) + (108493340779681/2000000000000 : ℝ)*(major1) + (108493340779681/2000000000000 : ℝ)*(major2) + (11932271967/100000000000000 : ℝ)*(sp2) + (7252126727658873/100000000000000 : ℝ)*(sp4) + (36260629614577/500000000000 : ℝ)*(sp5) + (7252113344129091/100000000000000 : ℝ)*(sp6) + (1798603558386053/50000000000000 : ℝ)*(sp7) + (1798603558386053/50000000000000 : ℝ)*(f.failure) + (7252126727658873/100000000000000 : ℝ)*(f.sum) + (340001402759/19520000000000000000000000 : ℝ)*base66 + (135462415047218249/9760000000000000000000000000000 : ℝ)*base67 + (80816374248461751/9760000000000000000000000000000 : ℝ)*base70 + (44279372374221751/9760000000000000000000000000000 : ℝ)*base72 + (135860649803/97600000000000000000000000 : ℝ)*base74 + (114220273626701751/9760000000000000000000000000000 : ℝ)*base76 + (31182748707538249/9760000000000000000000000000000 : ℝ)*base77 + (34418460172178249/9760000000000000000000000000000 : ℝ)*base79 + (498805390627/97600000000000000000000000 : ℝ)*base82 + (10270991/1250000000000000000000 : ℝ)*base89 + (10270991/1250000000000000000000 : ℝ)*base91 + (10270991/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1210_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10827/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1210_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1210_s5_0 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-4169269/19531250 : ℝ)*x 0 + (2696594049/5000000000 : ℝ)*x 1 + (1316363617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169269/19531250 : ℝ)^8403 ≤ (2595528135103/20000000000000 : ℝ)^6355 := by
    have hnat : (4169269 : ℕ)^8403*20000000000000^6355 ≤ 2595528135103^6355*19531250^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169269 19531250 2595528135103 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696594049/5000000000 : ℝ)^8403 ≤ (22100318548071/50000000000000 : ℝ)^6355 := by
    have hnat : (2696594049 : ℕ)^8403*50000000000000^6355 ≤ 22100318548071^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696594049 5000000000 22100318548071 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316363617/2500000000 : ℝ)^8403 ≤ (21410861107627/50000000000000 : ℝ)^6355 := by
    have hnat : (1316363617 : ℕ)^8403*50000000000000^6355 ≤ 21410861107627^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316363617 2500000000 21410861107627 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4169269/19531250 : ℝ), (2696594049/5000000000 : ℝ), (1316363617/2500000000 : ℝ)] ![(2595528135103/20000000000000 : ℝ), (22100318548071/50000000000000 : ℝ), (21410861107627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4169269/19531250 : ℝ)|^8403 ≤ (2595528135103/20000000000000 : ℝ)^6355
        have hw : |(-4169269/19531250 : ℝ)|=(4169269/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696594049/5000000000 : ℝ)|^8403 ≤ (22100318548071/50000000000000 : ℝ)^6355
        have hw : |(2696594049/5000000000 : ℝ)|=(2696594049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316363617/2500000000 : ℝ)|^8403 ≤ (21410861107627/50000000000000 : ℝ)^6355
        have hw : |(1316363617/2500000000 : ℝ)|=(1316363617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s5_1 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672411353/5000000000 : ℝ)*x 0 + (-274932153/1250000000 : ℝ)*x 1 + (2632727233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672411353/5000000000 : ℝ)^8403 ≤ (43677269070203/100000000000000 : ℝ)^6355 := by
    have hnat : (2672411353 : ℕ)^8403*100000000000000^6355 ≤ 43677269070203^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672411353 5000000000 43677269070203 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274932153/1250000000 : ℝ)^8403 ≤ (6750504362571/50000000000000 : ℝ)^6355 := by
    have hnat : (274932153 : ℕ)^8403*50000000000000^6355 ≤ 6750504362571^6355*1250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274932153 1250000000 6750504362571 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632727233/5000000000 : ℝ)^8403 ≤ (42821722193747/100000000000000 : ℝ)^6355 := by
    have hnat : (2632727233 : ℕ)^8403*100000000000000^6355 ≤ 42821722193747^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632727233 5000000000 42821722193747 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672411353/5000000000 : ℝ), (-274932153/1250000000 : ℝ), (2632727233/5000000000 : ℝ)] ![(43677269070203/100000000000000 : ℝ), (6750504362571/50000000000000 : ℝ), (42821722193747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672411353/5000000000 : ℝ)|^8403 ≤ (43677269070203/100000000000000 : ℝ)^6355
        have hw : |(2672411353/5000000000 : ℝ)|=(2672411353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-274932153/1250000000 : ℝ)|^8403 ≤ (6750504362571/50000000000000 : ℝ)^6355
        have hw : |(-274932153/1250000000 : ℝ)|=(274932153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632727233/5000000000 : ℝ)|^8403 ≤ (42821722193747/100000000000000 : ℝ)^6355
        have hw : |(2632727233/5000000000 : ℝ)|=(2632727233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s5_2 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668102839/1250000000 : ℝ)*x 0 + (2632727229/5000000000 : ℝ)*x 1 + (-1099728613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668102839/1250000000 : ℝ)^8403 ≤ (8735453827007/20000000000000 : ℝ)^6355 := by
    have hnat : (668102839 : ℕ)^8403*20000000000000^6355 ≤ 8735453827007^6355*1250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668102839 1250000000 8735453827007 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632727229/5000000000 : ℝ)^8403 ≤ (1070543052693/2500000000000 : ℝ)^6355 := by
    have hnat : (2632727229 : ℕ)^8403*2500000000000^6355 ≤ 1070543052693^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632727229 5000000000 1070543052693 2500000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099728613/5000000000 : ℝ)^8403 ≤ (108008069931/800000000000 : ℝ)^6355 := by
    have hnat : (1099728613 : ℕ)^8403*800000000000^6355 ≤ 108008069931^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099728613 5000000000 108008069931 800000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668102839/1250000000 : ℝ), (2632727229/5000000000 : ℝ), (-1099728613/5000000000 : ℝ)] ![(8735453827007/20000000000000 : ℝ), (1070543052693/2500000000000 : ℝ), (108008069931/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668102839/1250000000 : ℝ)|^8403 ≤ (8735453827007/20000000000000 : ℝ)^6355
        have hw : |(668102839/1250000000 : ℝ)|=(668102839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632727229/5000000000 : ℝ)|^8403 ≤ (1070543052693/2500000000000 : ℝ)^6355
        have hw : |(2632727229/5000000000 : ℝ)|=(2632727229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1099728613/5000000000 : ℝ)|^8403 ≤ (108008069931/800000000000 : ℝ)^6355
        have hw : |(-1099728613/5000000000 : ℝ)|=(1099728613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s5_3 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355111231/10000000000 : ℝ)*x 0 + (1057054277/2500000000 : ℝ)*x 1 + (1121433433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355111231/10000000000 : ℝ)^8403 ≤ (4164578202977/12500000000000 : ℝ)^6355 := by
    have hnat : (4355111231 : ℕ)^8403*12500000000000^6355 ≤ 4164578202977^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355111231 10000000000 4164578202977 12500000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057054277/2500000000 : ℝ)^8403 ≤ (4004889327267/12500000000000 : ℝ)^6355 := by
    have hnat : (1057054277 : ℕ)^8403*12500000000000^6355 ≤ 4004889327267^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057054277 2500000000 4004889327267 12500000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121433433/2500000000 : ℝ)^8403 ≤ (34644259747603/100000000000000 : ℝ)^6355 := by
    have hnat : (1121433433 : ℕ)^8403*100000000000000^6355 ≤ 34644259747603^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121433433 2500000000 34644259747603 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355111231/10000000000 : ℝ), (1057054277/2500000000 : ℝ), (1121433433/2500000000 : ℝ)] ![(4164578202977/12500000000000 : ℝ), (4004889327267/12500000000000 : ℝ), (34644259747603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355111231/10000000000 : ℝ)|^8403 ≤ (4164578202977/12500000000000 : ℝ)^6355
        have hw : |(4355111231/10000000000 : ℝ)|=(4355111231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057054277/2500000000 : ℝ)|^8403 ≤ (4004889327267/12500000000000 : ℝ)^6355
        have hw : |(1057054277/2500000000 : ℝ)|=(1057054277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121433433/2500000000 : ℝ)|^8403 ≤ (34644259747603/100000000000000 : ℝ)^6355
        have hw : |(1121433433/2500000000 : ℝ)|=(1121433433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s5_4 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134670101/10000000000 : ℝ)*x 0 + (1316445891/2500000000 : ℝ)*x 1 + (1348214571/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134670101/10000000000 : ℝ)^8403 ≤ (12977675828669/100000000000000 : ℝ)^6355 := by
    have hnat : (2134670101 : ℕ)^8403*100000000000000^6355 ≤ 12977675828669^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134670101 10000000000 12977675828669 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316445891/2500000000 : ℝ)^8403 ≤ (42825261162219/100000000000000 : ℝ)^6355 := by
    have hnat : (1316445891 : ℕ)^8403*100000000000000^6355 ≤ 42825261162219^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316445891 2500000000 42825261162219 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348214571/2500000000 : ℝ)^8403 ≤ (8839412599429/20000000000000 : ℝ)^6355 := by
    have hnat : (1348214571 : ℕ)^8403*20000000000000^6355 ≤ 8839412599429^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348214571 2500000000 8839412599429 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134670101/10000000000 : ℝ), (1316445891/2500000000 : ℝ), (1348214571/2500000000 : ℝ)] ![(12977675828669/100000000000000 : ℝ), (42825261162219/100000000000000 : ℝ), (8839412599429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134670101/10000000000 : ℝ)|^8403 ≤ (12977675828669/100000000000000 : ℝ)^6355
        have hw : |(-2134670101/10000000000 : ℝ)|=(2134670101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316445891/2500000000 : ℝ)|^8403 ≤ (42825261162219/100000000000000 : ℝ)^6355
        have hw : |(1316445891/2500000000 : ℝ)|=(1316445891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348214571/2500000000 : ℝ)|^8403 ≤ (8839412599429/20000000000000 : ℝ)^6355
        have hw : |(1348214571/2500000000 : ℝ)|=(1348214571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s5_5 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312302781/10000000000 : ℝ)*x 0 + (-2072053429/10000000000 : ℝ)*x 1 + (674107269/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312302781/10000000000 : ℝ)^8403 ≤ (8665244628307/20000000000000 : ℝ)^6355 := by
    have hnat : (5312302781 : ℕ)^8403*20000000000000^6355 ≤ 8665244628307^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312302781 10000000000 8665244628307 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2072053429/10000000000 : ℝ)^8403 ≤ (6238357638597/50000000000000 : ℝ)^6355 := by
    have hnat : (2072053429 : ℕ)^8403*50000000000000^6355 ≤ 6238357638597^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072053429 10000000000 6238357638597 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674107269/1250000000 : ℝ)^8403 ≤ (22098530783357/50000000000000 : ℝ)^6355 := by
    have hnat : (674107269 : ℕ)^8403*50000000000000^6355 ≤ 22098530783357^6355*1250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674107269 1250000000 22098530783357 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312302781/10000000000 : ℝ), (-2072053429/10000000000 : ℝ), (674107269/1250000000 : ℝ)] ![(8665244628307/20000000000000 : ℝ), (6238357638597/50000000000000 : ℝ), (22098530783357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312302781/10000000000 : ℝ)|^8403 ≤ (8665244628307/20000000000000 : ℝ)^6355
        have hw : |(5312302781/10000000000 : ℝ)|=(5312302781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2072053429/10000000000 : ℝ)|^8403 ≤ (6238357638597/50000000000000 : ℝ)^6355
        have hw : |(-2072053429/10000000000 : ℝ)|=(2072053429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674107269/1250000000 : ℝ)|^8403 ≤ (22098530783357/50000000000000 : ℝ)^6355
        have hw : |(674107269/1250000000 : ℝ)|=(674107269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s5_6 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312302711/10000000000 : ℝ)*x 0 + (5392858361/10000000000 : ℝ)*x 1 + (-51801331/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312302711/10000000000 : ℝ)^8403 ≤ (43326222386643/100000000000000 : ℝ)^6355 := by
    have hnat : (5312302711 : ℕ)^8403*100000000000000^6355 ≤ 43326222386643^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312302711 10000000000 43326222386643 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392858361/10000000000 : ℝ)^8403 ≤ (11049265957891/25000000000000 : ℝ)^6355 := by
    have hnat : (5392858361 : ℕ)^8403*25000000000000^6355 ≤ 11049265957891^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392858361 10000000000 11049265957891 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51801331/250000000 : ℝ)^8403 ≤ (1247671377239/10000000000000 : ℝ)^6355 := by
    have hnat : (51801331 : ℕ)^8403*10000000000000^6355 ≤ 1247671377239^6355*250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51801331 250000000 1247671377239 10000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312302711/10000000000 : ℝ), (5392858361/10000000000 : ℝ), (-51801331/250000000 : ℝ)] ![(43326222386643/100000000000000 : ℝ), (11049265957891/25000000000000 : ℝ), (1247671377239/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312302711/10000000000 : ℝ)|^8403 ≤ (43326222386643/100000000000000 : ℝ)^6355
        have hw : |(5312302711/10000000000 : ℝ)|=(5312302711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392858361/10000000000 : ℝ)|^8403 ≤ (11049265957891/25000000000000 : ℝ)^6355
        have hw : |(5392858361/10000000000 : ℝ)|=(5392858361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51801331/250000000 : ℝ)|^8403 ≤ (1247671377239/10000000000000 : ℝ)^6355
        have hw : |(-51801331/250000000 : ℝ)|=(51801331/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s5_7 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355121323/10000000000 : ℝ)*x 0 + (4485071079/10000000000 : ℝ)*x 1 + (2114441143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355121323/10000000000 : ℝ)^8403 ≤ (6663345541577/20000000000000 : ℝ)^6355 := by
    have hnat : (4355121323 : ℕ)^8403*20000000000000^6355 ≤ 6663345541577^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355121323 10000000000 6663345541577 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4485071079/10000000000 : ℝ)^8403 ≤ (34637492805911/100000000000000 : ℝ)^6355 := by
    have hnat : (4485071079 : ℕ)^8403*100000000000000^6355 ≤ 34637492805911^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485071079 10000000000 34637492805911 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114441143/5000000000 : ℝ)^8403 ≤ (1001430608639/3125000000000 : ℝ)^6355 := by
    have hnat : (2114441143 : ℕ)^8403*3125000000000^6355 ≤ 1001430608639^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114441143 5000000000 1001430608639 3125000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355121323/10000000000 : ℝ), (4485071079/10000000000 : ℝ), (2114441143/5000000000 : ℝ)] ![(6663345541577/20000000000000 : ℝ), (34637492805911/100000000000000 : ℝ), (1001430608639/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355121323/10000000000 : ℝ)|^8403 ≤ (6663345541577/20000000000000 : ℝ)^6355
        have hw : |(4355121323/10000000000 : ℝ)|=(4355121323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4485071079/10000000000 : ℝ)|^8403 ≤ (34637492805911/100000000000000 : ℝ)^6355
        have hw : |(4485071079/10000000000 : ℝ)|=(4485071079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114441143/5000000000 : ℝ)|^8403 ≤ (1001430608639/3125000000000 : ℝ)^6355
        have hw : |(2114441143/5000000000 : ℝ)|=(2114441143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1210_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11411/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14117/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5649/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5649/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5649/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5649/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5649/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5649/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5649/50000 : ℝ) ^ (4201/1024 : ℝ) ≤ (13028725990176357/100000000000000000000 : ℝ) := by
    have hpowers : (5649/50000 : ℝ)^4201 ≤ (13028725990176357/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5649 : ℕ)^4201*100000000000000000000^1024 ≤ 13028725990176357^1024*50000^4201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5649 50000 13028725990176357 100000000000000000000 4201 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5649/50000 : ℝ)) (X := (13028725990176357/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (4201/1024 : ℝ) ≤ (33621412480999249/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^4201 ≤ (33621412480999249/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2847 : ℕ)^4201*100000000000000000000^1024 ≤ 33621412480999249^1024*20000^4201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 33621412480999249 100000000000000000000 4201 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (33621412480999249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013028725990176357/50000000000000000000 : ℝ) ≤ (5000317545848389/5000000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (50013028725990176357/50000000000000000000 : ℝ)^1024 ≤ (5000317545848389/5000000000000000 : ℝ)^4201 := by
      have hnat : (50013028725990176357 : ℕ)^1024*5000000000000000^4201 ≤ 5000317545848389^4201*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013028725990176357 50000000000000000000 5000317545848389 5000000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000317545848389/5000000000000000 : ℝ)) (X := (50013028725990176357/50000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023325069235587803/50000000000000000000 : ℝ) ≤ (100011369035403/100000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (50023325069235587803/50000000000000000000 : ℝ)^1024 ≤ (100011369035403/100000000000000 : ℝ)^4201 := by
      have hnat : (50023325069235587803 : ℕ)^1024*100000000000000^4201 ≤ 100011369035403^4201*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023325069235587803 50000000000000000000 100011369035403 100000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100011369035403/100000000000000 : ℝ)) (X := (50023325069235587803/50000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033621412480999249/50000000000000000000 : ℝ) ≤ (5000819357691911/5000000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (50033621412480999249/50000000000000000000 : ℝ)^1024 ≤ (5000819357691911/5000000000000000 : ℝ)^4201 := by
      have hnat : (50033621412480999249 : ℕ)^1024*5000000000000000^4201 ≤ 5000819357691911^4201*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033621412480999249 50000000000000000000 5000819357691911 5000000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000819357691911/5000000000000000 : ℝ)) (X := (50033621412480999249/50000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13028725990176357/100000000000000000000 : ℝ) ≤ ((444856459452988089/445000000000000000 : ℝ)+2*(22809629251/13350000000000 : ℝ)*(5649/50000 : ℝ))^(4201/1024 : ℝ) := by
    rw [show (444856459452988089/445000000000000000 : ℝ)+2*(22809629251/13350000000000 : ℝ)*(5649/50000 : ℝ)=(5000317545848389/5000000000000000 : ℝ) by norm_num, show 1+2*(13028725990176357/100000000000000000000 : ℝ)=(50013028725990176357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33621412480999249/100000000000000000000 : ℝ)+(13028725990176357/100000000000000000000 : ℝ) ≤ ((444856459452988089/445000000000000000 : ℝ)+(22809629251/13350000000000 : ℝ)*((2847/20000 : ℝ)+(5649/50000 : ℝ)))^(4201/1024 : ℝ) := by
    rw [show (444856459452988089/445000000000000000 : ℝ)+(22809629251/13350000000000 : ℝ)*((2847/20000 : ℝ)+(5649/50000 : ℝ))=(100011369035403/100000000000000 : ℝ) by norm_num, show 1+(33621412480999249/100000000000000000000 : ℝ)+(13028725990176357/100000000000000000000 : ℝ)=(50023325069235587803/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33621412480999249/100000000000000000000 : ℝ) ≤ ((444856459452988089/445000000000000000 : ℝ)+2*(22809629251/13350000000000 : ℝ)*(2847/20000 : ℝ))^(4201/1024 : ℝ) := by
    rw [show (444856459452988089/445000000000000000 : ℝ)+2*(22809629251/13350000000000 : ℝ)*(2847/20000 : ℝ)=(5000819357691911/5000000000000000 : ℝ) by norm_num, show 1+2*(33621412480999249/100000000000000000000 : ℝ)=(50033621412480999249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (444856459452988089/445000000000000000 : ℝ)*(X 1 0+X 2 0)+(22809629251/13350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (444856459452988089/445000000000000000 : ℝ)) (alpha := (22809629251/13350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (444856459452988089/445000000000000000 : ℝ)*(X 0 1+X 2 1)+(22809629251/13350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (444856459452988089/445000000000000000 : ℝ)) (alpha := (22809629251/13350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (444856459452988089/445000000000000000 : ℝ)*(X 0 2+X 1 2)+(22809629251/13350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (444856459452988089/445000000000000000 : ℝ)) (alpha := (22809629251/13350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-4169269/19531250 : ℝ)*X 0 0+(2696594049/5000000000 : ℝ)*X 0 1+(1316363617/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672411353/5000000000 : ℝ)*X 1 0+(-274932153/1250000000 : ℝ)*X 1 1+(2632727233/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668102839/1250000000 : ℝ)*X 2 0+(2632727229/5000000000 : ℝ)*X 2 1+(-1099728613/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355111231/10000000000 : ℝ)*X 0 0+(1057054277/2500000000 : ℝ)*X 0 1+(1121433433/2500000000 : ℝ)*X 0 2+(4355111231/10000000000 : ℝ)*X 1 0+(1057054277/2500000000 : ℝ)*X 1 1+(1121433433/2500000000 : ℝ)*X 1 2+(4355111231/10000000000 : ℝ)*X 2 0+(1057054277/2500000000 : ℝ)*X 2 1+(1121433433/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2134670101/10000000000 : ℝ)*X 0 0+(1316445891/2500000000 : ℝ)*X 0 1+(1348214571/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312302781/10000000000 : ℝ)*X 1 0+(-2072053429/10000000000 : ℝ)*X 1 1+(674107269/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312302711/10000000000 : ℝ)*X 2 0+(5392858361/10000000000 : ℝ)*X 2 1+(-51801331/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355121323/10000000000 : ℝ)*X 0 0+(4485071079/10000000000 : ℝ)*X 0 1+(2114441143/5000000000 : ℝ)*X 0 2+(4355121323/10000000000 : ℝ)*X 1 0+(4485071079/10000000000 : ℝ)*X 1 1+(2114441143/5000000000 : ℝ)*X 1 2+(4355121323/10000000000 : ℝ)*X 2 0+(4485071079/10000000000 : ℝ)*X 2 1+(2114441143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3513127572490961529051/445000000000000000000000000 : ℝ) := by norm_num
    linear_combination (304288233/20000000000000 : ℝ)*(base19) + (14287189/1000000000000 : ℝ)*(base23) + (54255731/100000000000000 : ℝ)*(lower2) + (98986731/50000000000000 : ℝ)*(upper3) + (24205499/20000000000000 : ℝ)*(upper5) + (5856081176953931/100000000000000 : ℝ)*(major0) + (5856081176953931/100000000000000 : ℝ)*(major1) + (5856081176953931/100000000000000 : ℝ)*(major2) + (1565766920298733/20000000000000 : ℝ)*(sp0) + (782887395747893/10000000000000 : ℝ)*(sp1) + (1565774810040239/20000000000000 : ℝ)*(sp2) + (3883264404227741/100000000000000 : ℝ)*(sp3) + (4087742643/10000000000000 : ℝ)*(sp4) + (22207604397/100000000000000 : ℝ)*(sp7) + (1941643305916069/50000000000000 : ℝ)*(f.failure) + (1565775095784019/20000000000000 : ℝ)*(f.sum) + (1359773310529/667500000000000000000000000 : ℝ)*base66 + (462269144611216423/133500000000000000000000000000000 : ℝ)*base68 + (725662020453283577/133500000000000000000000000000000 : ℝ)*base69 + (206301805605283577/133500000000000000000000000000000 : ℝ)*base71 + (9213925418423/1335000000000000000000000000 : ℝ)*base74 + (2515174780113283577/133500000000000000000000000000000 : ℝ)*base75 + (10629855104716423/133500000000000000000000000000000 : ℝ)*base78 + (1422946040881216423/133500000000000000000000000000000 : ℝ)*base80 + (4353478791889/667500000000000000000000000 : ℝ)*base82 + (110257/1250000000000000000000 : ℝ)*base90 + (110257/1250000000000000000000 : ℝ)*base92 + (110257/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42169713109295496592164221/4450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1801617/800000000000 : ℝ)*(base19) + (1232804739/100000000000000 : ℝ)*(base23) + (44559/80000000000 : ℝ)*(lower2) + (15227/12500000000000 : ℝ)*(lower3) + (101560999/20000000000000 : ℝ)*(lower4) + (167101791/100000000000000 : ℝ)*(lower5) + (1177273684836263/20000000000000 : ℝ)*(major0) + (1177273684836263/20000000000000 : ℝ)*(major1) + (1177273684836263/20000000000000 : ℝ)*(major2) + (42511783843/100000000000000 : ℝ)*(sp2) + (314774633224309/4000000000000 : ℝ)*(sp4) + (7869365605405601/100000000000000 : ℝ)*(sp5) + (7869322086019143/100000000000000 : ℝ)*(sp6) + (780674140375379/20000000000000 : ℝ)*(sp7) + (780674140375379/20000000000000 : ℝ)*(f.failure) + (314774633224309/4000000000000 : ℝ)*(f.sum) + (1387836319297/133500000000000000000000000 : ℝ)*base66 + (202060492789385779/26700000000000000000000000000000 : ℝ)*base68 + (225438325664885779/26700000000000000000000000000000 : ℝ)*base70 + (73623499021914221/26700000000000000000000000000000 : ℝ)*base71 + (850707348433/133500000000000000000000000 : ℝ)*base74 + (495072693233285779/26700000000000000000000000000000 : ℝ)*base76 + (124825919941685779/26700000000000000000000000000000 : ℝ)*base78 + (231710515596714221/26700000000000000000000000000000 : ℝ)*base79 + (93981990109/133500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1367687/500000000000000000000 : ℝ)*base90 + (1367687/500000000000000000000 : ℝ)*base92 + (1367687/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1210_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11411/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1210_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1210_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11411/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1210_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1210_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1210_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11411/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1210_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

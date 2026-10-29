-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1359_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:11:03.057059+00:00
-- url     : https://prove2.me/submissions/69bd5d8c-7ca7-4d56-9ecf-1508c41edf7a

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
theorem support_rectangle_w1359_s0_0 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-449784723/2500000000 : ℝ)*x 0 + (2994803351/5000000000 : ℝ)*x 1 + (4814948913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449784723/2500000000 : ℝ)^4319 ≤ (10557430738629/100000000000000 : ℝ)^3295 := by
    have hnat : (449784723 : ℕ)^4319*100000000000000^3295 ≤ 10557430738629^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449784723 2500000000 10557430738629 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2994803351/5000000000 : ℝ)^4319 ≤ (51076309452559/100000000000000 : ℝ)^3295 := by
    have hnat : (2994803351 : ℕ)^4319*100000000000000^3295 ≤ 51076309452559^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2994803351 5000000000 51076309452559 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4814948913/10000000000 : ℝ)^4319 ≤ (38366259793111/100000000000000 : ℝ)^3295 := by
    have hnat : (4814948913 : ℕ)^4319*100000000000000^3295 ≤ 38366259793111^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814948913 10000000000 38366259793111 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-449784723/2500000000 : ℝ), (2994803351/5000000000 : ℝ), (4814948913/10000000000 : ℝ)] ![(10557430738629/100000000000000 : ℝ), (51076309452559/100000000000000 : ℝ), (38366259793111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-449784723/2500000000 : ℝ)|^4319 ≤ (10557430738629/100000000000000 : ℝ)^3295
        have hw : |(-449784723/2500000000 : ℝ)|=(449784723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2994803351/5000000000 : ℝ)|^4319 ≤ (51076309452559/100000000000000 : ℝ)^3295
        have hw : |(2994803351/5000000000 : ℝ)|=(2994803351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4814948913/10000000000 : ℝ)|^4319 ≤ (38366259793111/100000000000000 : ℝ)^3295
        have hw : |(4814948913/10000000000 : ℝ)|=(4814948913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s0_1 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1374977439/2500000000 : ℝ)*x 0 + (-616497079/2500000000 : ℝ)*x 1 + (4814949407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1374977439/2500000000 : ℝ)^4319 ≤ (22836779246523/50000000000000 : ℝ)^3295 := by
    have hnat : (1374977439 : ℕ)^4319*50000000000000^3295 ≤ 22836779246523^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374977439 2500000000 22836779246523 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (616497079/2500000000 : ℝ)^4319 ≤ (15960176543899/100000000000000 : ℝ)^3295 := by
    have hnat : (616497079 : ℕ)^4319*100000000000000^3295 ≤ 15960176543899^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      616497079 2500000000 15960176543899 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4814949407/10000000000 : ℝ)^4319 ≤ (38366264952669/100000000000000 : ℝ)^3295 := by
    have hnat : (4814949407 : ℕ)^4319*100000000000000^3295 ≤ 38366264952669^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814949407 10000000000 38366264952669 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1374977439/2500000000 : ℝ), (-616497079/2500000000 : ℝ), (4814949407/10000000000 : ℝ)] ![(22836779246523/50000000000000 : ℝ), (15960176543899/100000000000000 : ℝ), (38366264952669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1374977439/2500000000 : ℝ)|^4319 ≤ (22836779246523/50000000000000 : ℝ)^3295
        have hw : |(1374977439/2500000000 : ℝ)|=(1374977439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-616497079/2500000000 : ℝ)|^4319 ≤ (15960176543899/100000000000000 : ℝ)^3295
        have hw : |(-616497079/2500000000 : ℝ)|=(616497079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4814949407/10000000000 : ℝ)|^4319 ≤ (38366264952669/100000000000000 : ℝ)^3295
        have hw : |(4814949407/10000000000 : ℝ)|=(4814949407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s0_2 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2749954807/5000000000 : ℝ)*x 0 + (192597957/400000000 : ℝ)*x 1 + (-2465989091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2749954807/5000000000 : ℝ)^4319 ≤ (22836778473673/50000000000000 : ℝ)^3295 := by
    have hnat : (2749954807 : ℕ)^4319*50000000000000^3295 ≤ 22836778473673^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749954807 5000000000 22836778473673 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192597957/400000000 : ℝ)^4319 ≤ (9591564979611/25000000000000 : ℝ)^3295 := by
    have hnat : (192597957 : ℕ)^4319*25000000000000^3295 ≤ 9591564979611^3295*400000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192597957 400000000 9591564979611 25000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2465989091/10000000000 : ℝ)^4319 ≤ (15960183118603/100000000000000 : ℝ)^3295 := by
    have hnat : (2465989091 : ℕ)^4319*100000000000000^3295 ≤ 15960183118603^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2465989091 10000000000 15960183118603 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2749954807/5000000000 : ℝ), (192597957/400000000 : ℝ), (-2465989091/10000000000 : ℝ)] ![(22836778473673/50000000000000 : ℝ), (9591564979611/25000000000000 : ℝ), (15960183118603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2749954807/5000000000 : ℝ)|^4319 ≤ (22836778473673/50000000000000 : ℝ)^3295
        have hw : |(2749954807/5000000000 : ℝ)|=(2749954807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(192597957/400000000 : ℝ)|^4319 ≤ (9591564979611/25000000000000 : ℝ)^3295
        have hw : |(192597957/400000000 : ℝ)|=(192597957/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2465989091/10000000000 : ℝ)|^4319 ≤ (15960183118603/100000000000000 : ℝ)^3295
        have hw : |(-2465989091/10000000000 : ℝ)|=(2465989091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s0_3 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (835242603/2000000000 : ℝ)*x 0 + (621153139/2000000000 : ℝ)*x 1 + (558191699/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835242603/2000000000 : ℝ)^4319 ≤ (7959243548821/25000000000000 : ℝ)^3295 := by
    have hnat : (835242603 : ℕ)^4319*25000000000000^3295 ≤ 7959243548821^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835242603 2000000000 7959243548821 25000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (621153139/2000000000 : ℝ)^4319 ≤ (10797369800597/50000000000000 : ℝ)^3295 := by
    have hnat : (621153139 : ℕ)^4319*50000000000000^3295 ≤ 10797369800597^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621153139 2000000000 10797369800597 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (558191699/1000000000 : ℝ)^4319 ≤ (46568286185777/100000000000000 : ℝ)^3295 := by
    have hnat : (558191699 : ℕ)^4319*100000000000000^3295 ≤ 46568286185777^3295*1000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558191699 1000000000 46568286185777 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(835242603/2000000000 : ℝ), (621153139/2000000000 : ℝ), (558191699/1000000000 : ℝ)] ![(7959243548821/25000000000000 : ℝ), (10797369800597/50000000000000 : ℝ), (46568286185777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(835242603/2000000000 : ℝ)|^4319 ≤ (7959243548821/25000000000000 : ℝ)^3295
        have hw : |(835242603/2000000000 : ℝ)|=(835242603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(621153139/2000000000 : ℝ)|^4319 ≤ (10797369800597/50000000000000 : ℝ)^3295
        have hw : |(621153139/2000000000 : ℝ)|=(621153139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(558191699/1000000000 : ℝ)|^4319 ≤ (46568286185777/100000000000000 : ℝ)^3295
        have hw : |(558191699/1000000000 : ℝ)|=(558191699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s0_4 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1803507103/10000000000 : ℝ)*x 0 + (484515041/1000000000 : ℝ)*x 1 + (5958326257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1803507103/10000000000 : ℝ)^4319 ≤ (529552114921/5000000000000 : ℝ)^3295 := by
    have hnat : (1803507103 : ℕ)^4319*5000000000000^3295 ≤ 529552114921^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803507103 10000000000 529552114921 5000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484515041/1000000000 : ℝ)^4319 ≤ (9670501203143/25000000000000 : ℝ)^3295 := by
    have hnat : (484515041 : ℕ)^4319*25000000000000^3295 ≤ 9670501203143^3295*1000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484515041 1000000000 9670501203143 25000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5958326257/10000000000 : ℝ)^4319 ≤ (50726952883651/100000000000000 : ℝ)^3295 := by
    have hnat : (5958326257 : ℕ)^4319*100000000000000^3295 ≤ 50726952883651^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5958326257 10000000000 50726952883651 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1803507103/10000000000 : ℝ), (484515041/1000000000 : ℝ), (5958326257/10000000000 : ℝ)] ![(529552114921/5000000000000 : ℝ), (9670501203143/25000000000000 : ℝ), (50726952883651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1803507103/10000000000 : ℝ)|^4319 ≤ (529552114921/5000000000000 : ℝ)^3295
        have hw : |(-1803507103/10000000000 : ℝ)|=(1803507103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(484515041/1000000000 : ℝ)|^4319 ≤ (9670501203143/25000000000000 : ℝ)^3295
        have hw : |(484515041/1000000000 : ℝ)|=(484515041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5958326257/10000000000 : ℝ)|^4319 ≤ (50726952883651/100000000000000 : ℝ)^3295
        have hw : |(5958326257/10000000000 : ℝ)|=(5958326257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s0_5 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5179672443/10000000000 : ℝ)*x 0 + (-1322613161/10000000000 : ℝ)*x 1 + (1489581409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5179672443/10000000000 : ℝ)^4319 ≤ (21109838514569/50000000000000 : ℝ)^3295 := by
    have hnat : (5179672443 : ℕ)^4319*50000000000000^3295 ≤ 21109838514569^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179672443 10000000000 21109838514569 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1322613161/10000000000 : ℝ)^4319 ≤ (7053377000313/100000000000000 : ℝ)^3295 := by
    have hnat : (1322613161 : ℕ)^4319*100000000000000^3295 ≤ 7053377000313^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322613161 10000000000 7053377000313 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1489581409/2500000000 : ℝ)^4319 ≤ (50726945953641/100000000000000 : ℝ)^3295 := by
    have hnat : (1489581409 : ℕ)^4319*100000000000000^3295 ≤ 50726945953641^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489581409 2500000000 50726945953641 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5179672443/10000000000 : ℝ), (-1322613161/10000000000 : ℝ), (1489581409/2500000000 : ℝ)] ![(21109838514569/50000000000000 : ℝ), (7053377000313/100000000000000 : ℝ), (50726945953641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5179672443/10000000000 : ℝ)|^4319 ≤ (21109838514569/50000000000000 : ℝ)^3295
        have hw : |(5179672443/10000000000 : ℝ)|=(5179672443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1322613161/10000000000 : ℝ)|^4319 ≤ (7053377000313/100000000000000 : ℝ)^3295
        have hw : |(-1322613161/10000000000 : ℝ)|=(1322613161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1489581409/2500000000 : ℝ)|^4319 ≤ (50726945953641/100000000000000 : ℝ)^3295
        have hw : |(1489581409/2500000000 : ℝ)|=(1489581409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s0_6 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2589836123/5000000000 : ℝ)*x 0 + (119166529/200000000 : ℝ)*x 1 + (-1322612163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589836123/5000000000 : ℝ)^4319 ≤ (21109837462179/50000000000000 : ℝ)^3295 := by
    have hnat : (2589836123 : ℕ)^4319*50000000000000^3295 ≤ 21109837462179^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589836123 5000000000 21109837462179 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119166529/200000000 : ℝ)^4319 ≤ (25363477518711/50000000000000 : ℝ)^3295 := by
    have hnat : (119166529 : ℕ)^4319*50000000000000^3295 ≤ 25363477518711^3295*200000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119166529 200000000 25363477518711 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1322612163/10000000000 : ℝ)^4319 ≤ (1410674004811/20000000000000 : ℝ)^3295 := by
    have hnat : (1322612163 : ℕ)^4319*20000000000000^3295 ≤ 1410674004811^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322612163 10000000000 1410674004811 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589836123/5000000000 : ℝ), (119166529/200000000 : ℝ), (-1322612163/10000000000 : ℝ)] ![(21109837462179/50000000000000 : ℝ), (25363477518711/50000000000000 : ℝ), (1410674004811/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589836123/5000000000 : ℝ)|^4319 ≤ (21109837462179/50000000000000 : ℝ)^3295
        have hw : |(2589836123/5000000000 : ℝ)|=(2589836123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(119166529/200000000 : ℝ)|^4319 ≤ (25363477518711/50000000000000 : ℝ)^3295
        have hw : |(119166529/200000000 : ℝ)|=(119166529/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1322612163/10000000000 : ℝ)|^4319 ≤ (1410674004811/20000000000000 : ℝ)^3295
        have hw : |(-1322612163/10000000000 : ℝ)|=(1322612163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s0_7 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (523177141/1250000000 : ℝ)*x 0 + (1379563629/2500000000 : ℝ)*x 1 + (3171704157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523177141/1250000000 : ℝ)^4319 ≤ (31928978362607/100000000000000 : ℝ)^3295 := by
    have hnat : (523177141 : ℕ)^4319*100000000000000^3295 ≤ 31928978362607^3295*1250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523177141 1250000000 31928978362607 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379563629/2500000000 : ℝ)^4319 ≤ (2293667429657/5000000000000 : ℝ)^3295 := by
    have hnat : (1379563629 : ℕ)^4319*5000000000000^3295 ≤ 2293667429657^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379563629 2500000000 2293667429657 5000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3171704157/10000000000 : ℝ)^4319 ≤ (22197673031501/100000000000000 : ℝ)^3295 := by
    have hnat : (3171704157 : ℕ)^4319*100000000000000^3295 ≤ 22197673031501^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3171704157 10000000000 22197673031501 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523177141/1250000000 : ℝ), (1379563629/2500000000 : ℝ), (3171704157/10000000000 : ℝ)] ![(31928978362607/100000000000000 : ℝ), (2293667429657/5000000000000 : ℝ), (22197673031501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523177141/1250000000 : ℝ)|^4319 ≤ (31928978362607/100000000000000 : ℝ)^3295
        have hw : |(523177141/1250000000 : ℝ)|=(523177141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379563629/2500000000 : ℝ)|^4319 ≤ (2293667429657/5000000000000 : ℝ)^3295
        have hw : |(1379563629/2500000000 : ℝ)|=(1379563629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3171704157/10000000000 : ℝ)|^4319 ≤ (22197673031501/100000000000000 : ℝ)^3295
        have hw : |(3171704157/10000000000 : ℝ)|=(3171704157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1359_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1541/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26749/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
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
  have hpowlo : (0 : ℝ) ^ (2159/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2159 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2159*1^512 ≤ 0^512*1^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2159/512 : ℝ) ≤ (2098784339650817263/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2159 ≤ (2098784339650817263/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2159*100000000000000000000^512 ≤ 2098784339650817263^512*5^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2098784339650817263 100000000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2098784339650817263/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2159 := by
      have hnat : (1 : ℕ)^512*1^2159 ≤ 1^2159*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102098784339650817263/100000000000000000000 : ℝ) ≤ (10049378407597507/10000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (102098784339650817263/100000000000000000000 : ℝ)^512 ≤ (10049378407597507/10000000000000000 : ℝ)^2159 := by
      have hnat : (102098784339650817263 : ℕ)^512*10000000000000000^2159 ≤ 10049378407597507^2159*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102098784339650817263 100000000000000000000 10049378407597507 10000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10049378407597507/10000000000000000 : ℝ)) (X := (102098784339650817263/100000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52098784339650817263/50000000000000000000 : ℝ) ≤ (5049378407597507/5000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (52098784339650817263/50000000000000000000 : ℝ)^512 ≤ (5049378407597507/5000000000000000 : ℝ)^2159 := by
      have hnat : (52098784339650817263 : ℕ)^512*5000000000000000^2159 ≤ 5049378407597507^2159*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52098784339650817263 50000000000000000000 5049378407597507 5000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5049378407597507/5000000000000000 : ℝ)) (X := (52098784339650817263/50000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(49378407597507/4000000000000000 : ℝ)*(0 : ℝ))^(2159/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(49378407597507/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2098784339650817263/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(49378407597507/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2159/512 : ℝ) := by
    rw [show (1 : ℝ)+(49378407597507/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10049378407597507/10000000000000000 : ℝ) by norm_num, show 1+(2098784339650817263/100000000000000000000 : ℝ)+(0 : ℝ)=(102098784339650817263/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2098784339650817263/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(49378407597507/4000000000000000 : ℝ)*(2/5 : ℝ))^(2159/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(49378407597507/4000000000000000 : ℝ)*(2/5 : ℝ)=(5049378407597507/5000000000000000 : ℝ) by norm_num, show 1+2*(2098784339650817263/100000000000000000000 : ℝ)=(52098784339650817263/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(49378407597507/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49378407597507/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(49378407597507/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49378407597507/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(49378407597507/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49378407597507/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-449784723/2500000000 : ℝ)*X 0 0+(2994803351/5000000000 : ℝ)*X 0 1+(4814948913/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1374977439/2500000000 : ℝ)*X 1 0+(-616497079/2500000000 : ℝ)*X 1 1+(4814949407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2749954807/5000000000 : ℝ)*X 2 0+(192597957/400000000 : ℝ)*X 2 1+(-2465989091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((835242603/2000000000 : ℝ)*X 0 0+(621153139/2000000000 : ℝ)*X 0 1+(558191699/1000000000 : ℝ)*X 0 2+(835242603/2000000000 : ℝ)*X 1 0+(621153139/2000000000 : ℝ)*X 1 1+(558191699/1000000000 : ℝ)*X 1 2+(835242603/2000000000 : ℝ)*X 2 0+(621153139/2000000000 : ℝ)*X 2 1+(558191699/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1803507103/10000000000 : ℝ)*X 0 0+(484515041/1000000000 : ℝ)*X 0 1+(5958326257/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5179672443/10000000000 : ℝ)*X 1 0+(-1322613161/10000000000 : ℝ)*X 1 1+(1489581409/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2589836123/5000000000 : ℝ)*X 2 0+(119166529/200000000 : ℝ)*X 2 1+(-1322612163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((523177141/1250000000 : ℝ)*X 0 0+(1379563629/2500000000 : ℝ)*X 0 1+(3171704157/10000000000 : ℝ)*X 0 2+(523177141/1250000000 : ℝ)*X 1 0+(1379563629/2500000000 : ℝ)*X 1 1+(3171704157/10000000000 : ℝ)*X 1 2+(523177141/1250000000 : ℝ)*X 2 0+(1379563629/2500000000 : ℝ)*X 2 1+(3171704157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (131897360747112108504669/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30387303/20000000000000 : ℝ)*(base1) + (1225601483/100000000000000 : ℝ)*(base19) + (240724327/20000000000000 : ℝ)*(base23) + (70157/31250000000 : ℝ)*(upper3) + (28997/160000000000 : ℝ)*(upper5) + (156896961790611/25000000000000 : ℝ)*(major0) + (156896961790611/25000000000000 : ℝ)*(major1) + (156896961790611/25000000000000 : ℝ)*(major2) + (425658113912171/50000000000000 : ℝ)*(sp0) + (851318172695127/100000000000000 : ℝ)*(sp1) + (34052727786999/4000000000000 : ℝ)*(sp2) + (403853930254347/100000000000000 : ℝ)*(sp3) + (3322408783/100000000000000 : ℝ)*(sp4) + (1018987131/50000000000000 : ℝ)*(sp7) + (403856120165123/100000000000000 : ℝ)*(f.failure) + (85131939829661/10000000000000 : ℝ)*(f.sum) + (104030748206777/50000000000000000000000000000 : ℝ)*base65 + (45563147493223/100000000000000000000000000000 : ℝ)*base68 + (457236514493223/100000000000000000000000000000 : ℝ)*base70 + (211620824306777/100000000000000000000000000000 : ℝ)*base71 + (26767438356777/50000000000000000000000000000 : ℝ)*base73 + (419135064306777/100000000000000000000000000000 : ℝ)*base75 + (530945760506777/100000000000000000000000000000 : ℝ)*base77 + (280570776406777/100000000000000000000000000000 : ℝ)*base79 + (255532947343223/50000000000000000000000000000 : ℝ)*base82 + (7238899/1000000000000000000000 : ℝ)*base90 + (7238899/1000000000000000000000 : ℝ)*base92 + (7238899/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (387581394586533168014823/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30856713/10000000000000 : ℝ)*(base19) + (628979983/100000000000000 : ℝ)*(base23) + (28318249/10000000000000 : ℝ)*(base39) + (29651981/100000000000000 : ℝ)*(upper2) + (150154583/100000000000000 : ℝ)*(upper5) + (662243269333937/100000000000000 : ℝ)*(major0) + (662243269333937/100000000000000 : ℝ)*(major1) + (82780373268931/12500000000000 : ℝ)*(major2) + (602833519/100000000000000 : ℝ)*(sp1) + (940863241/100000000000000 : ℝ)*(sp2) + (898329057495691/100000000000000 : ℝ)*(sp4) + (449164073047521/50000000000000 : ℝ)*(sp5) + (898327770834957/100000000000000 : ℝ)*(sp6) + (426157068795891/100000000000000 : ℝ)*(sp7) + (426157068795891/100000000000000 : ℝ)*(f.failure) + (898329340678181/100000000000000 : ℝ)*(f.sum) + (33065370187039/80000000000000000000000000000 : ℝ)*base65 + (202880137144983/50000000000000000000000000000 : ℝ)*base68 + (1221677282095059/400000000000000000000000000000 : ℝ)*base69 + (253419284744983/50000000000000000000000000000 : ℝ)*base72 + (183245040987039/80000000000000000000000000000 : ℝ)*base73 + (1813592738895059/400000000000000000000000000000 : ℝ)*base75 + (1723581105904941/400000000000000000000000000000 : ℝ)*base78 + (2409040660704941/400000000000000000000000000000 : ℝ)*base80 + (99921678695059/200000000000000000000000000000 : ℝ)*base81 + (2204317/1000000000000000000000 : ℝ)*base89 + (2204317/1000000000000000000000 : ℝ)*base91 + (7795683/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1359_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1541/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26749/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1359_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1359_s1_0 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1981506433/10000000000 : ℝ)*x 0 + (5634584533/10000000000 : ℝ)*x 1 + (5053162807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1981506433/10000000000 : ℝ)^4319 ≤ (5990871946141/50000000000000 : ℝ)^3295 := by
    have hnat : (1981506433 : ℕ)^4319*50000000000000^3295 ≤ 5990871946141^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981506433 10000000000 5990871946141 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5634584533/10000000000 : ℝ)^4319 ≤ (1885802776421/4000000000000 : ℝ)^3295 := by
    have hnat : (5634584533 : ℕ)^4319*4000000000000^3295 ≤ 1885802776421^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5634584533 10000000000 1885802776421 4000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5053162807/10000000000 : ℝ)^4319 ≤ (40873186676661/100000000000000 : ℝ)^3295 := by
    have hnat : (5053162807 : ℕ)^4319*100000000000000^3295 ≤ 40873186676661^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5053162807 10000000000 40873186676661 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1981506433/10000000000 : ℝ), (5634584533/10000000000 : ℝ), (5053162807/10000000000 : ℝ)] ![(5990871946141/50000000000000 : ℝ), (1885802776421/4000000000000 : ℝ), (40873186676661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1981506433/10000000000 : ℝ)|^4319 ≤ (5990871946141/50000000000000 : ℝ)^3295
        have hw : |(-1981506433/10000000000 : ℝ)|=(1981506433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5634584533/10000000000 : ℝ)|^4319 ≤ (1885802776421/4000000000000 : ℝ)^3295
        have hw : |(5634584533/10000000000 : ℝ)|=(5634584533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5053162807/10000000000 : ℝ)|^4319 ≤ (40873186676661/100000000000000 : ℝ)^3295
        have hw : |(5053162807/10000000000 : ℝ)|=(5053162807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s1_1 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (675493559/1250000000 : ℝ)*x 0 + (-2291319907/10000000000 : ℝ)*x 1 + (1010632731/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675493559/1250000000 : ℝ)^4319 ≤ (22315921272433/50000000000000 : ℝ)^3295 := by
    have hnat : (675493559 : ℕ)^4319*50000000000000^3295 ≤ 22315921272433^3295*1250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675493559 1250000000 22315921272433 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2291319907/10000000000 : ℝ)^4319 ≤ (14494961777613/100000000000000 : ℝ)^3295 := by
    have hnat : (2291319907 : ℕ)^4319*100000000000000^3295 ≤ 14494961777613^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291319907 10000000000 14494961777613 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010632731/2000000000 : ℝ)^4319 ≤ (40873195667471/100000000000000 : ℝ)^3295 := by
    have hnat : (1010632731 : ℕ)^4319*100000000000000^3295 ≤ 40873195667471^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010632731 2000000000 40873195667471 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675493559/1250000000 : ℝ), (-2291319907/10000000000 : ℝ), (1010632731/2000000000 : ℝ)] ![(22315921272433/50000000000000 : ℝ), (14494961777613/100000000000000 : ℝ), (40873195667471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675493559/1250000000 : ℝ)|^4319 ≤ (22315921272433/50000000000000 : ℝ)^3295
        have hw : |(675493559/1250000000 : ℝ)|=(675493559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2291319907/10000000000 : ℝ)|^4319 ≤ (14494961777613/100000000000000 : ℝ)^3295
        have hw : |(-2291319907/10000000000 : ℝ)|=(2291319907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010632731/2000000000 : ℝ)|^4319 ≤ (40873195667471/100000000000000 : ℝ)^3295
        have hw : |(1010632731/2000000000 : ℝ)|=(1010632731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s1_2 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350987153/2500000000 : ℝ)*x 0 + (5053162973/10000000000 : ℝ)*x 1 + (-2291320597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350987153/2500000000 : ℝ)^4319 ≤ (44631844060483/100000000000000 : ℝ)^3295 := by
    have hnat : (1350987153 : ℕ)^4319*100000000000000^3295 ≤ 44631844060483^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350987153 2500000000 44631844060483 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5053162973/10000000000 : ℝ)^4319 ≤ (20436594218327/50000000000000 : ℝ)^3295 := by
    have hnat : (5053162973 : ℕ)^4319*50000000000000^3295 ≤ 20436594218327^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5053162973 10000000000 20436594218327 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2291320597/10000000000 : ℝ)^4319 ≤ (14494967499091/100000000000000 : ℝ)^3295 := by
    have hnat : (2291320597 : ℕ)^4319*100000000000000^3295 ≤ 14494967499091^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291320597 10000000000 14494967499091 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350987153/2500000000 : ℝ), (5053162973/10000000000 : ℝ), (-2291320597/10000000000 : ℝ)] ![(44631844060483/100000000000000 : ℝ), (20436594218327/50000000000000 : ℝ), (14494967499091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350987153/2500000000 : ℝ)|^4319 ≤ (44631844060483/100000000000000 : ℝ)^3295
        have hw : |(1350987153/2500000000 : ℝ)|=(1350987153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5053162973/10000000000 : ℝ)|^4319 ≤ (20436594218327/50000000000000 : ℝ)^3295
        have hw : |(5053162973/10000000000 : ℝ)|=(5053162973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2291320597/10000000000 : ℝ)|^4319 ≤ (14494967499091/100000000000000 : ℝ)^3295
        have hw : |(-2291320597/10000000000 : ℝ)|=(2291320597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s1_3 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2144636443/5000000000 : ℝ)*x 0 + (116147927/312500000 : ℝ)*x 1 + (4942353617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144636443/5000000000 : ℝ)^4319 ≤ (2060715967439/6250000000000 : ℝ)^3295 := by
    have hnat : (2144636443 : ℕ)^4319*6250000000000^3295 ≤ 2060715967439^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144636443 5000000000 2060715967439 6250000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116147927/312500000 : ℝ)^4319 ≤ (13663087210109/50000000000000 : ℝ)^3295 := by
    have hnat : (116147927 : ℕ)^4319*50000000000000^3295 ≤ 13663087210109^3295*312500000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116147927 312500000 13663087210109 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4942353617/10000000000 : ℝ)^4319 ≤ (620349532629/1562500000000 : ℝ)^3295 := by
    have hnat : (4942353617 : ℕ)^4319*1562500000000^3295 ≤ 620349532629^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4942353617 10000000000 620349532629 1562500000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2144636443/5000000000 : ℝ), (116147927/312500000 : ℝ), (4942353617/10000000000 : ℝ)] ![(2060715967439/6250000000000 : ℝ), (13663087210109/50000000000000 : ℝ), (620349532629/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2144636443/5000000000 : ℝ)|^4319 ≤ (2060715967439/6250000000000 : ℝ)^3295
        have hw : |(2144636443/5000000000 : ℝ)|=(2144636443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(116147927/312500000 : ℝ)|^4319 ≤ (13663087210109/50000000000000 : ℝ)^3295
        have hw : |(116147927/312500000 : ℝ)|=(116147927/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4942353617/10000000000 : ℝ)|^4319 ≤ (620349532629/1562500000000 : ℝ)^3295
        have hw : |(4942353617/10000000000 : ℝ)|=(4942353617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s1_4 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-991006347/5000000000 : ℝ)*x 0 + (2530181777/5000000000 : ℝ)*x 1 + (140681363/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (991006347/5000000000 : ℝ)^4319 ≤ (1198575666021/10000000000000 : ℝ)^3295 := by
    have hnat : (991006347 : ℕ)^4319*10000000000000^3295 ≤ 1198575666021^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991006347 5000000000 1198575666021 10000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2530181777/5000000000 : ℝ)^4319 ≤ (10237387141589/25000000000000 : ℝ)^3295 := by
    have hnat : (2530181777 : ℕ)^4319*25000000000000^3295 ≤ 10237387141589^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2530181777 5000000000 10237387141589 25000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140681363/250000000 : ℝ)^4319 ≤ (5883086845263/12500000000000 : ℝ)^3295 := by
    have hnat : (140681363 : ℕ)^4319*12500000000000^3295 ≤ 5883086845263^3295*250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140681363 250000000 5883086845263 12500000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-991006347/5000000000 : ℝ), (2530181777/5000000000 : ℝ), (140681363/250000000 : ℝ)] ![(1198575666021/10000000000000 : ℝ), (10237387141589/25000000000000 : ℝ), (5883086845263/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-991006347/5000000000 : ℝ)|^4319 ≤ (1198575666021/10000000000000 : ℝ)^3295
        have hw : |(-991006347/5000000000 : ℝ)|=(991006347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2530181777/5000000000 : ℝ)|^4319 ≤ (10237387141589/25000000000000 : ℝ)^3295
        have hw : |(2530181777/5000000000 : ℝ)|=(2530181777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140681363/250000000 : ℝ)|^4319 ≤ (5883086845263/12500000000000 : ℝ)^3295
        have hw : |(140681363/250000000 : ℝ)|=(140681363/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s1_5 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210114621/400000000 : ℝ)*x 0 + (-858614427/5000000000 : ℝ)*x 1 + (703406823/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210114621/400000000 : ℝ)^4319 ≤ (8600679039533/20000000000000 : ℝ)^3295 := by
    have hnat : (210114621 : ℕ)^4319*20000000000000^3295 ≤ 8600679039533^3295*400000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210114621 400000000 8600679039533 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (858614427/5000000000 : ℝ)^4319 ≤ (9931909320309/100000000000000 : ℝ)^3295 := by
    have hnat : (858614427 : ℕ)^4319*100000000000000^3295 ≤ 9931909320309^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858614427 5000000000 9931909320309 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (703406823/1250000000 : ℝ)^4319 ≤ (47064695463731/100000000000000 : ℝ)^3295 := by
    have hnat : (703406823 : ℕ)^4319*100000000000000^3295 ≤ 47064695463731^3295*1250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      703406823 1250000000 47064695463731 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210114621/400000000 : ℝ), (-858614427/5000000000 : ℝ), (703406823/1250000000 : ℝ)] ![(8600679039533/20000000000000 : ℝ), (9931909320309/100000000000000 : ℝ), (47064695463731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210114621/400000000 : ℝ)|^4319 ≤ (8600679039533/20000000000000 : ℝ)^3295
        have hw : |(210114621/400000000 : ℝ)|=(210114621/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-858614427/5000000000 : ℝ)|^4319 ≤ (9931909320309/100000000000000 : ℝ)^3295
        have hw : |(-858614427/5000000000 : ℝ)|=(858614427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(703406823/1250000000 : ℝ)|^4319 ≤ (47064695463731/100000000000000 : ℝ)^3295
        have hw : |(703406823/1250000000 : ℝ)|=(703406823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s1_6 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626432709/5000000000 : ℝ)*x 0 + (5627254669/10000000000 : ℝ)*x 1 + (-429307221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626432709/5000000000 : ℝ)^4319 ≤ (5375424256183/12500000000000 : ℝ)^3295 := by
    have hnat : (2626432709 : ℕ)^4319*12500000000000^3295 ≤ 5375424256183^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626432709 5000000000 5375424256183 12500000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5627254669/10000000000 : ℝ)^4319 ≤ (47064696395579/100000000000000 : ℝ)^3295 := by
    have hnat : (5627254669 : ℕ)^4319*100000000000000^3295 ≤ 47064696395579^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5627254669 10000000000 47064696395579 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429307221/2500000000 : ℝ)^4319 ≤ (4965954773871/50000000000000 : ℝ)^3295 := by
    have hnat : (429307221 : ℕ)^4319*50000000000000^3295 ≤ 4965954773871^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429307221 2500000000 4965954773871 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626432709/5000000000 : ℝ), (5627254669/10000000000 : ℝ), (-429307221/2500000000 : ℝ)] ![(5375424256183/12500000000000 : ℝ), (47064696395579/100000000000000 : ℝ), (4965954773871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626432709/5000000000 : ℝ)|^4319 ≤ (5375424256183/12500000000000 : ℝ)^3295
        have hw : |(2626432709/5000000000 : ℝ)|=(2626432709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5627254669/10000000000 : ℝ)|^4319 ≤ (47064696395579/100000000000000 : ℝ)^3295
        have hw : |(5627254669/10000000000 : ℝ)|=(5627254669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-429307221/2500000000 : ℝ)|^4319 ≤ (4965954773871/50000000000000 : ℝ)^3295
        have hw : |(-429307221/2500000000 : ℝ)|=(429307221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s1_7 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2145170343/5000000000 : ℝ)*x 0 + (4927176013/10000000000 : ℝ)*x 1 + (3732182519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145170343/5000000000 : ℝ)^4319 ≤ (32982214901033/100000000000000 : ℝ)^3295 := by
    have hnat : (2145170343 : ℕ)^4319*100000000000000^3295 ≤ 32982214901033^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145170343 5000000000 32982214901033 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4927176013/10000000000 : ℝ)^4319 ≤ (7908526568839/20000000000000 : ℝ)^3295 := by
    have hnat : (4927176013 : ℕ)^4319*20000000000000^3295 ≤ 7908526568839^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4927176013 10000000000 7908526568839 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3732182519/10000000000 : ℝ)^4319 ≤ (3434394030231/12500000000000 : ℝ)^3295 := by
    have hnat : (3732182519 : ℕ)^4319*12500000000000^3295 ≤ 3434394030231^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3732182519 10000000000 3434394030231 12500000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2145170343/5000000000 : ℝ), (4927176013/10000000000 : ℝ), (3732182519/10000000000 : ℝ)] ![(32982214901033/100000000000000 : ℝ), (7908526568839/20000000000000 : ℝ), (3434394030231/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2145170343/5000000000 : ℝ)|^4319 ≤ (32982214901033/100000000000000 : ℝ)^3295
        have hw : |(2145170343/5000000000 : ℝ)|=(2145170343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4927176013/10000000000 : ℝ)|^4319 ≤ (7908526568839/20000000000000 : ℝ)^3295
        have hw : |(4927176013/10000000000 : ℝ)|=(4927176013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3732182519/10000000000 : ℝ)|^4319 ≤ (3434394030231/12500000000000 : ℝ)^3295
        have hw : |(3732182519/10000000000 : ℝ)|=(3732182519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1359_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1541/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3523/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3867/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1541/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1541/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1541/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1541/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1541/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1541/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (1541/100000 : ℝ) ^ (2159/512 : ℝ) ≤ (456417014367/20000000000000000000 : ℝ) := by
    have hpowers : (1541/100000 : ℝ)^2159 ≤ (456417014367/20000000000000000000 : ℝ)^512 := by
      have hnat : (1541 : ℕ)^2159*20000000000000000000^512 ≤ 456417014367^512*100000^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1541 100000 456417014367 20000000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1541/100000 : ℝ)) (X := (456417014367/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26749/100000 : ℝ) ^ (2159/512 : ℝ) ≤ (384655786142295849/100000000000000000000 : ℝ) := by
    have hpowers : (26749/100000 : ℝ)^2159 ≤ (384655786142295849/100000000000000000000 : ℝ)^512 := by
      have hnat : (26749 : ℕ)^2159*100000000000000000000^512 ≤ 384655786142295849^512*100000^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26749 100000 384655786142295849 100000000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26749/100000 : ℝ)) (X := (384655786142295849/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000456417014367/10000000000000000000 : ℝ) ≤ (2000000021647569/2000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (10000000456417014367/10000000000000000000 : ℝ)^512 ≤ (2000000021647569/2000000000000000 : ℝ)^2159 := by
      have hnat : (10000000456417014367 : ℕ)^512*2000000000000000^2159 ≤ 2000000021647569^2159*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000456417014367 10000000000000000000 2000000021647569 2000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000021647569/2000000000000000 : ℝ)) (X := (10000000456417014367/10000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25096164517056841921/25000000000000000000 : ℝ) ≤ (10009108690461627/10000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (25096164517056841921/25000000000000000000 : ℝ)^512 ≤ (10009108690461627/10000000000000000 : ℝ)^2159 := by
      have hnat : (25096164517056841921 : ℕ)^512*10000000000000000^2159 ≤ 10009108690461627^2159*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25096164517056841921 25000000000000000000 10009108690461627 10000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009108690461627/10000000000000000 : ℝ)) (X := (25096164517056841921/25000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50384655786142295849/50000000000000000000 : ℝ) ≤ (10018217272685409/10000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (50384655786142295849/50000000000000000000 : ℝ)^512 ≤ (10018217272685409/10000000000000000 : ℝ)^2159 := by
      have hnat : (50384655786142295849 : ℕ)^512*10000000000000000^2159 ≤ 10018217272685409^2159*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50384655786142295849 50000000000000000000 10018217272685409 10000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10018217272685409/10000000000000000 : ℝ)) (X := (50384655786142295849/50000000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(456417014367/20000000000000000000 : ℝ) ≤ ((2739694892152672833/2740000000000000000 : ℝ)+2*(4554291111891/1260400000000000 : ℝ)*(1541/100000 : ℝ))^(2159/512 : ℝ) := by
    rw [show (2739694892152672833/2740000000000000000 : ℝ)+2*(4554291111891/1260400000000000 : ℝ)*(1541/100000 : ℝ)=(2000000021647569/2000000000000000 : ℝ) by norm_num, show 1+2*(456417014367/20000000000000000000 : ℝ)=(10000000456417014367/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(384655786142295849/100000000000000000000 : ℝ)+(456417014367/20000000000000000000 : ℝ) ≤ ((2739694892152672833/2740000000000000000 : ℝ)+(4554291111891/1260400000000000 : ℝ)*((26749/100000 : ℝ)+(1541/100000 : ℝ)))^(2159/512 : ℝ) := by
    rw [show (2739694892152672833/2740000000000000000 : ℝ)+(4554291111891/1260400000000000 : ℝ)*((26749/100000 : ℝ)+(1541/100000 : ℝ))=(10009108690461627/10000000000000000 : ℝ) by norm_num, show 1+(384655786142295849/100000000000000000000 : ℝ)+(456417014367/20000000000000000000 : ℝ)=(25096164517056841921/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(384655786142295849/100000000000000000000 : ℝ) ≤ ((2739694892152672833/2740000000000000000 : ℝ)+2*(4554291111891/1260400000000000 : ℝ)*(26749/100000 : ℝ))^(2159/512 : ℝ) := by
    rw [show (2739694892152672833/2740000000000000000 : ℝ)+2*(4554291111891/1260400000000000 : ℝ)*(26749/100000 : ℝ)=(10018217272685409/10000000000000000 : ℝ) by norm_num, show 1+2*(384655786142295849/100000000000000000000 : ℝ)=(50384655786142295849/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2739694892152672833/2740000000000000000 : ℝ)*(X 1 0+X 2 0)+(4554291111891/1260400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (1541/100000 : ℝ)) (hi := (26749/100000 : ℝ)) (c := (2739694892152672833/2740000000000000000 : ℝ)) (alpha := (4554291111891/1260400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2739694892152672833/2740000000000000000 : ℝ)*(X 0 1+X 2 1)+(4554291111891/1260400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (1541/100000 : ℝ)) (hi := (26749/100000 : ℝ)) (c := (2739694892152672833/2740000000000000000 : ℝ)) (alpha := (4554291111891/1260400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2739694892152672833/2740000000000000000 : ℝ)*(X 0 2+X 1 2)+(4554291111891/1260400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (1541/100000 : ℝ)) (hi := (26749/100000 : ℝ)) (c := (2739694892152672833/2740000000000000000 : ℝ)) (alpha := (4554291111891/1260400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1981506433/10000000000 : ℝ)*X 0 0+(5634584533/10000000000 : ℝ)*X 0 1+(5053162807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((675493559/1250000000 : ℝ)*X 1 0+(-2291319907/10000000000 : ℝ)*X 1 1+(1010632731/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1350987153/2500000000 : ℝ)*X 2 0+(5053162973/10000000000 : ℝ)*X 2 1+(-2291320597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2144636443/5000000000 : ℝ)*X 0 0+(116147927/312500000 : ℝ)*X 0 1+(4942353617/10000000000 : ℝ)*X 0 2+(2144636443/5000000000 : ℝ)*X 1 0+(116147927/312500000 : ℝ)*X 1 1+(4942353617/10000000000 : ℝ)*X 1 2+(2144636443/5000000000 : ℝ)*X 2 0+(116147927/312500000 : ℝ)*X 2 1+(4942353617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-991006347/5000000000 : ℝ)*X 0 0+(2530181777/5000000000 : ℝ)*X 0 1+(140681363/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((210114621/400000000 : ℝ)*X 1 0+(-858614427/5000000000 : ℝ)*X 1 1+(703406823/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2626432709/5000000000 : ℝ)*X 2 0+(5627254669/10000000000 : ℝ)*X 2 1+(-429307221/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2145170343/5000000000 : ℝ)*X 0 0+(4927176013/10000000000 : ℝ)*X 0 1+(3732182519/10000000000 : ℝ)*X 0 2+(2145170343/5000000000 : ℝ)*X 1 0+(4927176013/10000000000 : ℝ)*X 1 1+(3732182519/10000000000 : ℝ)*X 1 2+(2145170343/5000000000 : ℝ)*X 2 0+(4927176013/10000000000 : ℝ)*X 2 1+(3732182519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (121938969319921895526327/15755000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1403737/50000000000000 : ℝ)*(base1) + (3834907/25000000000000 : ℝ)*(base16) + (1195295507/100000000000000 : ℝ)*(base19) + (49031/3906250000 : ℝ)*(base23) + (236234921/100000000000000 : ℝ)*(upper3) + (158491391351539/12500000000000 : ℝ)*(major0) + (158491391351539/12500000000000 : ℝ)*(major1) + (158491391351539/12500000000000 : ℝ)*(major2) + (1719933009320907/100000000000000 : ℝ)*(sp0) + (1719940361395121/100000000000000 : ℝ)*(sp1) + (107496269802291/6250000000000 : ℝ)*(sp2) + (16318327698273/2000000000000 : ℝ)*(sp3) + (342620673/4000000000000 : ℝ)*(sp4) + (808776649/20000000000000 : ℝ)*(sp7) + (815920431604369/100000000000000 : ℝ)*(f.failure) + (1719941572030257/100000000000000 : ℝ)*(f.sum) + (13655828894697/15755000000000000000000000000 : ℝ)*base66 + (3946406554644130299/787750000000000000000000000000000 : ℝ)*base68 + (4664856523416130299/787750000000000000000000000000000 : ℝ)*base70 + (1826068575198130299/787750000000000000000000000000000 : ℝ)*base72 + (2363483834631/492343750000000000000000000 : ℝ)*base74 + (3737031080032369701/787750000000000000000000000000000 : ℝ)*base75 + (1714303362211869701/787750000000000000000000000000000 : ℝ)*base77 + (4900962732141619701/787750000000000000000000000000000 : ℝ)*base79 + (53795376237117/15755000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2966303/1000000000000000000000 : ℝ)*base89 + (2966303/1000000000000000000000 : ℝ)*base91 + (2966303/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (661379142227450850175364739/137000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25978991/50000000000000 : ℝ)*(base1) + (987563477/100000000000000 : ℝ)*(base19) + (950160849/100000000000000 : ℝ)*(base23) + (114389651/100000000000000 : ℝ)*(upper3) + (104550677/100000000000000 : ℝ)*(upper5) + (1300416128404587/100000000000000 : ℝ)*(major0) + (1300416128404587/100000000000000 : ℝ)*(major1) + (1300416128404587/100000000000000 : ℝ)*(major2) + (2608456851/50000000000000 : ℝ)*(sp1) + (2582896187/50000000000000 : ℝ)*(sp2) + (441001861845487/25000000000000 : ℝ)*(sp4) + (1764001190946787/100000000000000 : ℝ)*(sp5) + (1764001279470743/100000000000000 : ℝ)*(sp6) + (836824648507721/100000000000000 : ℝ)*(sp7) + (836824700465703/100000000000000 : ℝ)*(f.failure) + (352801479084793/20000000000000 : ℝ)*(f.sum) + (45518067148137/63020000000000000000000000000 : ℝ)*base65 + (33275796612876995667/6302000000000000000000000000000000 : ℝ)*base68 + (640981584264995667/6302000000000000000000000000000000 : ℝ)*base70 + (24066674937996995667/6302000000000000000000000000000000 : ℝ)*base72 + (180453348529797/63020000000000000000000000000 : ℝ)*base73 + (48626410204580995667/6302000000000000000000000000000000 : ℝ)*base76 + (27749368016782995667/6302000000000000000000000000000000 : ℝ)*base78 + (36562250395530995667/6302000000000000000000000000000000 : ℝ)*base80 + (254777715554837/63020000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1995561/1000000000000000000000 : ℝ)*base89 + (1995561/1000000000000000000000 : ℝ)*base91 + (1995561/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1359_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1541/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3523/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3867/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1359_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1359_s2_0 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2020201277/10000000000 : ℝ)*x 0 + (684397759/1250000000 : ℝ)*x 1 + (1037551031/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2020201277/10000000000 : ℝ)^4319 ≤ (6144682244567/50000000000000 : ℝ)^3295 := by
    have hnat : (2020201277 : ℕ)^4319*50000000000000^3295 ≤ 6144682244567^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020201277 10000000000 6144682244567 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684397759/1250000000 : ℝ)^4319 ≤ (22702290269719/50000000000000 : ℝ)^3295 := by
    have hnat : (684397759 : ℕ)^4319*50000000000000^3295 ≤ 22702290269719^3295*1250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684397759 1250000000 22702290269719 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037551031/2000000000 : ℝ)^4319 ≤ (42306054951871/100000000000000 : ℝ)^3295 := by
    have hnat : (1037551031 : ℕ)^4319*100000000000000^3295 ≤ 42306054951871^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037551031 2000000000 42306054951871 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2020201277/10000000000 : ℝ), (684397759/1250000000 : ℝ), (1037551031/2000000000 : ℝ)] ![(6144682244567/50000000000000 : ℝ), (22702290269719/50000000000000 : ℝ), (42306054951871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2020201277/10000000000 : ℝ)|^4319 ≤ (6144682244567/50000000000000 : ℝ)^3295
        have hw : |(-2020201277/10000000000 : ℝ)|=(2020201277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(684397759/1250000000 : ℝ)|^4319 ≤ (22702290269719/50000000000000 : ℝ)^3295
        have hw : |(684397759/1250000000 : ℝ)|=(684397759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037551031/2000000000 : ℝ)|^4319 ≤ (42306054951871/100000000000000 : ℝ)^3295
        have hw : |(1037551031/2000000000 : ℝ)|=(1037551031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s2_1 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364767363/10000000000 : ℝ)*x 0 + (-2168580889/10000000000 : ℝ)*x 1 + (5187755507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364767363/10000000000 : ℝ)^4319 ≤ (44208153002879/100000000000000 : ℝ)^3295 := by
    have hnat : (5364767363 : ℕ)^4319*100000000000000^3295 ≤ 44208153002879^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364767363 10000000000 44208153002879 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2168580889/10000000000 : ℝ)^4319 ≤ (168572353303/1250000000000 : ℝ)^3295 := by
    have hnat : (2168580889 : ℕ)^4319*1250000000000^3295 ≤ 168572353303^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168580889 10000000000 168572353303 1250000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5187755507/10000000000 : ℝ)^4319 ≤ (21153029357259/50000000000000 : ℝ)^3295 := by
    have hnat : (5187755507 : ℕ)^4319*50000000000000^3295 ≤ 21153029357259^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187755507 10000000000 21153029357259 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364767363/10000000000 : ℝ), (-2168580889/10000000000 : ℝ), (5187755507/10000000000 : ℝ)] ![(44208153002879/100000000000000 : ℝ), (168572353303/1250000000000 : ℝ), (21153029357259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364767363/10000000000 : ℝ)|^4319 ≤ (44208153002879/100000000000000 : ℝ)^3295
        have hw : |(5364767363/10000000000 : ℝ)|=(5364767363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2168580889/10000000000 : ℝ)|^4319 ≤ (168572353303/1250000000000 : ℝ)^3295
        have hw : |(-2168580889/10000000000 : ℝ)|=(2168580889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5187755507/10000000000 : ℝ)|^4319 ≤ (21153029357259/50000000000000 : ℝ)^3295
        have hw : |(5187755507/10000000000 : ℝ)|=(5187755507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s2_2 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2682383709/5000000000 : ℝ)*x 0 + (5187755439/10000000000 : ℝ)*x 1 + (-433716181/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682383709/5000000000 : ℝ)^4319 ≤ (8841630719391/20000000000000 : ℝ)^3295 := by
    have hnat : (2682383709 : ℕ)^4319*20000000000000^3295 ≤ 8841630719391^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682383709 5000000000 8841630719391 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5187755439/10000000000 : ℝ)^4319 ≤ (42306057987643/100000000000000 : ℝ)^3295 := by
    have hnat : (5187755439 : ℕ)^4319*100000000000000^3295 ≤ 42306057987643^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187755439 10000000000 42306057987643 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433716181/2000000000 : ℝ)^4319 ≤ (13485788394661/100000000000000 : ℝ)^3295 := by
    have hnat : (433716181 : ℕ)^4319*100000000000000^3295 ≤ 13485788394661^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433716181 2000000000 13485788394661 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682383709/5000000000 : ℝ), (5187755439/10000000000 : ℝ), (-433716181/2000000000 : ℝ)] ![(8841630719391/20000000000000 : ℝ), (42306057987643/100000000000000 : ℝ), (13485788394661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682383709/5000000000 : ℝ)|^4319 ≤ (8841630719391/20000000000000 : ℝ)^3295
        have hw : |(2682383709/5000000000 : ℝ)|=(2682383709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5187755439/10000000000 : ℝ)|^4319 ≤ (42306057987643/100000000000000 : ℝ)^3295
        have hw : |(5187755439/10000000000 : ℝ)|=(5187755439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-433716181/2000000000 : ℝ)|^4319 ≤ (13485788394661/100000000000000 : ℝ)^3295
        have hw : |(-433716181/2000000000 : ℝ)|=(433716181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s2_3 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (67443501/156250000 : ℝ)*x 0 + (502909573/1250000000 : ℝ)*x 1 + (2314582627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67443501/156250000 : ℝ)^4319 ≤ (16622445941051/50000000000000 : ℝ)^3295 := by
    have hnat : (67443501 : ℕ)^4319*50000000000000^3295 ≤ 16622445941051^3295*156250000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67443501 156250000 16622445941051 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502909573/1250000000 : ℝ)^4319 ≤ (3789689712533/12500000000000 : ℝ)^3295 := by
    have hnat : (502909573 : ℕ)^4319*12500000000000^3295 ≤ 3789689712533^3295*1250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502909573 1250000000 3789689712533 12500000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2314582627/5000000000 : ℝ)^4319 ≤ (2277349399803/6250000000000 : ℝ)^3295 := by
    have hnat : (2314582627 : ℕ)^4319*6250000000000^3295 ≤ 2277349399803^3295*5000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2314582627 5000000000 2277349399803 6250000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67443501/156250000 : ℝ), (502909573/1250000000 : ℝ), (2314582627/5000000000 : ℝ)] ![(16622445941051/50000000000000 : ℝ), (3789689712533/12500000000000 : ℝ), (2277349399803/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67443501/156250000 : ℝ)|^4319 ≤ (16622445941051/50000000000000 : ℝ)^3295
        have hw : |(67443501/156250000 : ℝ)|=(67443501/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502909573/1250000000 : ℝ)|^4319 ≤ (3789689712533/12500000000000 : ℝ)^3295
        have hw : |(502909573/1250000000 : ℝ)|=(502909573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2314582627/5000000000 : ℝ)|^4319 ≤ (2277349399803/6250000000000 : ℝ)^3295
        have hw : |(2314582627/5000000000 : ℝ)|=(2314582627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s2_4 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-252532809/1250000000 : ℝ)*x 0 + (5189524773/10000000000 : ℝ)*x 1 + (5473396791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252532809/1250000000 : ℝ)^4319 ≤ (1228985244501/10000000000000 : ℝ)^3295 := by
    have hnat : (252532809 : ℕ)^4319*10000000000000^3295 ≤ 1228985244501^3295*1250000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252532809 1250000000 1228985244501 10000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5189524773/10000000000 : ℝ)^4319 ≤ (1058124300021/2500000000000 : ℝ)^3295 := by
    have hnat : (5189524773 : ℕ)^4319*2500000000000^3295 ≤ 1058124300021^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189524773 10000000000 1058124300021 2500000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5473396791/10000000000 : ℝ)^4319 ≤ (4538517554763/10000000000000 : ℝ)^3295 := by
    have hnat : (5473396791 : ℕ)^4319*10000000000000^3295 ≤ 4538517554763^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473396791 10000000000 4538517554763 10000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-252532809/1250000000 : ℝ), (5189524773/10000000000 : ℝ), (5473396791/10000000000 : ℝ)] ![(1228985244501/10000000000000 : ℝ), (1058124300021/2500000000000 : ℝ), (4538517554763/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-252532809/1250000000 : ℝ)|^4319 ≤ (1228985244501/10000000000000 : ℝ)^3295
        have hw : |(-252532809/1250000000 : ℝ)|=(252532809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5189524773/10000000000 : ℝ)|^4319 ≤ (1058124300021/2500000000000 : ℝ)^3295
        have hw : |(5189524773/10000000000 : ℝ)|=(5189524773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5473396791/10000000000 : ℝ)|^4319 ≤ (4538517554763/10000000000000 : ℝ)^3295
        have hw : |(5473396791/10000000000 : ℝ)|=(5473396791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s2_5 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058109627/2000000000 : ℝ)*x 0 + (-1882939319/10000000000 : ℝ)*x 1 + (5473396747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058109627/2000000000 : ℝ)^4319 ≤ (43408211756077/100000000000000 : ℝ)^3295 := by
    have hnat : (1058109627 : ℕ)^4319*100000000000000^3295 ≤ 43408211756077^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058109627 2000000000 43408211756077 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1882939319/10000000000 : ℝ)^4319 ≤ (11206613160301/100000000000000 : ℝ)^3295 := by
    have hnat : (1882939319 : ℕ)^4319*100000000000000^3295 ≤ 11206613160301^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882939319 10000000000 11206613160301 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5473396747/10000000000 : ℝ)^4319 ≤ (45385175069399/100000000000000 : ℝ)^3295 := by
    have hnat : (5473396747 : ℕ)^4319*100000000000000^3295 ≤ 45385175069399^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473396747 10000000000 45385175069399 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058109627/2000000000 : ℝ), (-1882939319/10000000000 : ℝ), (5473396747/10000000000 : ℝ)] ![(43408211756077/100000000000000 : ℝ), (11206613160301/100000000000000 : ℝ), (45385175069399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058109627/2000000000 : ℝ)|^4319 ≤ (43408211756077/100000000000000 : ℝ)^3295
        have hw : |(1058109627/2000000000 : ℝ)|=(1058109627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1882939319/10000000000 : ℝ)|^4319 ≤ (11206613160301/100000000000000 : ℝ)^3295
        have hw : |(-1882939319/10000000000 : ℝ)|=(1882939319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5473396747/10000000000 : ℝ)|^4319 ≤ (45385175069399/100000000000000 : ℝ)^3295
        have hw : |(5473396747/10000000000 : ℝ)|=(5473396747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s2_6 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058109621/2000000000 : ℝ)*x 0 + (1094679359/2000000000 : ℝ)*x 1 + (-1882939293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058109621/2000000000 : ℝ)^4319 ≤ (8681642286687/20000000000000 : ℝ)^3295 := by
    have hnat : (1058109621 : ℕ)^4319*20000000000000^3295 ≤ 8681642286687^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058109621 2000000000 8681642286687 20000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094679359/2000000000 : ℝ)^4319 ≤ (22692587795553/50000000000000 : ℝ)^3295 := by
    have hnat : (1094679359 : ℕ)^4319*50000000000000^3295 ≤ 22692587795553^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094679359 2000000000 22692587795553 50000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1882939293/10000000000 : ℝ)^4319 ≤ (11206612957467/100000000000000 : ℝ)^3295 := by
    have hnat : (1882939293 : ℕ)^4319*100000000000000^3295 ≤ 11206612957467^3295*10000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882939293 10000000000 11206612957467 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058109621/2000000000 : ℝ), (1094679359/2000000000 : ℝ), (-1882939293/10000000000 : ℝ)] ![(8681642286687/20000000000000 : ℝ), (22692587795553/50000000000000 : ℝ), (11206612957467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058109621/2000000000 : ℝ)|^4319 ≤ (8681642286687/20000000000000 : ℝ)^3295
        have hw : |(1058109621/2000000000 : ℝ)|=(1058109621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1094679359/2000000000 : ℝ)|^4319 ≤ (22692587795553/50000000000000 : ℝ)^3295
        have hw : |(1094679359/2000000000 : ℝ)|=(1094679359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1882939293/10000000000 : ℝ)|^4319 ≤ (11206612957467/100000000000000 : ℝ)^3295
        have hw : |(-1882939293/10000000000 : ℝ)|=(1882939293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1359_s2_7 (p : ℝ) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (863302671/2000000000 : ℝ)*x 0 + (1156358877/2500000000 : ℝ)*x 1 + (251689959/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863302671/2000000000 : ℝ)^4319 ≤ (33246197159883/100000000000000 : ℝ)^3295 := by
    have hnat : (863302671 : ℕ)^4319*100000000000000^3295 ≤ 33246197159883^3295*2000000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863302671 2000000000 33246197159883 100000000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1156358877/2500000000 : ℝ)^4319 ≤ (2274944596063/6250000000000 : ℝ)^3295 := by
    have hnat : (1156358877 : ℕ)^4319*6250000000000^3295 ≤ 2274944596063^3295*2500000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156358877 2500000000 2274944596063 6250000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251689959/625000000 : ℝ)^4319 ≤ (1897168080703/6250000000000 : ℝ)^3295 := by
    have hnat : (251689959 : ℕ)^4319*6250000000000^3295 ≤ 1897168080703^3295*625000000^4319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251689959 625000000 1897168080703 6250000000000 4319 3295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4319/1024 : ℝ)) 4319 3295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863302671/2000000000 : ℝ), (1156358877/2500000000 : ℝ), (251689959/625000000 : ℝ)] ![(33246197159883/100000000000000 : ℝ), (2274944596063/6250000000000 : ℝ), (1897168080703/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863302671/2000000000 : ℝ)|^4319 ≤ (33246197159883/100000000000000 : ℝ)^3295
        have hw : |(863302671/2000000000 : ℝ)|=(863302671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1156358877/2500000000 : ℝ)|^4319 ≤ (2274944596063/6250000000000 : ℝ)^3295
        have hw : |(1156358877/2500000000 : ℝ)|=(1156358877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251689959/625000000 : ℝ)|^4319 ≤ (1897168080703/6250000000000 : ℝ)^3295
        have hw : |(251689959/625000000 : ℝ)|=(251689959/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1359_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3867/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3523/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9961/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8019/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3867/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3523/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3867/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3523/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3867/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3523/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3867/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3523/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3867/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3523/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3867/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3523/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3523/50000 : ℝ) ^ (2159/512 : ℝ) ≤ (173347719524439/12500000000000000000 : ℝ) := by
    have hpowers : (3523/50000 : ℝ)^2159 ≤ (173347719524439/12500000000000000000 : ℝ)^512 := by
      have hnat : (3523 : ℕ)^2159*12500000000000000000^512 ≤ 173347719524439^512*50000^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3523 50000 173347719524439 12500000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3523/50000 : ℝ)) (X := (173347719524439/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3867/20000 : ℝ) ^ (2159/512 : ℝ) ≤ (12233996904208289/12500000000000000000 : ℝ) := by
    have hpowers : (3867/20000 : ℝ)^2159 ≤ (12233996904208289/12500000000000000000 : ℝ)^512 := by
      have hnat : (3867 : ℕ)^2159*12500000000000000000^512 ≤ 12233996904208289^512*20000^2159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3867 20000 12233996904208289 12500000000000000000 2159 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3867/20000 : ℝ)) (X := (12233996904208289/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250173347719524439/6250000000000000000 : ℝ) ≤ (10000065773482889/10000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (6250173347719524439/6250000000000000000 : ℝ)^512 ≤ (10000065773482889/10000000000000000 : ℝ)^2159 := by
      have hnat : (6250173347719524439 : ℕ)^512*10000000000000000^2159 ≤ 10000065773482889^2159*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250173347719524439 6250000000000000000 10000065773482889 10000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000065773482889/10000000000000000 : ℝ)) (X := (6250173347719524439/6250000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (1564050918077966591/1562500000000000000 : ℝ) ≤ (5001176499633963/5000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (1564050918077966591/1562500000000000000 : ℝ)^512 ≤ (5001176499633963/5000000000000000 : ℝ)^2159 := by
      have hnat : (1564050918077966591 : ℕ)^512*5000000000000000^2159 ≤ 5001176499633963^2159*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1564050918077966591 1562500000000000000 5001176499633963 5000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001176499633963/5000000000000000 : ℝ)) (X := (1564050918077966591/1562500000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6262233996904208289/6250000000000000000 : ℝ) ≤ (10004640225052963/10000000000000000 : ℝ) ^ (2159/512 : ℝ) := by
    have hpowers : (6262233996904208289/6250000000000000000 : ℝ)^512 ≤ (10004640225052963/10000000000000000 : ℝ)^2159 := by
      have hnat : (6262233996904208289 : ℕ)^512*10000000000000000^2159 ≤ 10004640225052963^2159*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6262233996904208289 6250000000000000000 10004640225052963 10000000000000000 512 2159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004640225052963/10000000000000000 : ℝ)) (X := (6262233996904208289/6250000000000000000 : ℝ)) (by norm_num) 2159 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(173347719524439/12500000000000000000 : ℝ) ≤ ((122858576704568481517/122890000000000000000 : ℝ)+2*(2287225785037/1228900000000000 : ℝ)*(3523/50000 : ℝ))^(2159/512 : ℝ) := by
    rw [show (122858576704568481517/122890000000000000000 : ℝ)+2*(2287225785037/1228900000000000 : ℝ)*(3523/50000 : ℝ)=(10000065773482889/10000000000000000 : ℝ) by norm_num, show 1+2*(173347719524439/12500000000000000000 : ℝ)=(6250173347719524439/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12233996904208289/12500000000000000000 : ℝ)+(173347719524439/12500000000000000000 : ℝ) ≤ ((122858576704568481517/122890000000000000000 : ℝ)+(2287225785037/1228900000000000 : ℝ)*((3867/20000 : ℝ)+(3523/50000 : ℝ)))^(2159/512 : ℝ) := by
    rw [show (122858576704568481517/122890000000000000000 : ℝ)+(2287225785037/1228900000000000 : ℝ)*((3867/20000 : ℝ)+(3523/50000 : ℝ))=(5001176499633963/5000000000000000 : ℝ) by norm_num, show 1+(12233996904208289/12500000000000000000 : ℝ)+(173347719524439/12500000000000000000 : ℝ)=(1564050918077966591/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12233996904208289/12500000000000000000 : ℝ) ≤ ((122858576704568481517/122890000000000000000 : ℝ)+2*(2287225785037/1228900000000000 : ℝ)*(3867/20000 : ℝ))^(2159/512 : ℝ) := by
    rw [show (122858576704568481517/122890000000000000000 : ℝ)+2*(2287225785037/1228900000000000 : ℝ)*(3867/20000 : ℝ)=(10004640225052963/10000000000000000 : ℝ) by norm_num, show 1+2*(12233996904208289/12500000000000000000 : ℝ)=(6262233996904208289/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (122858576704568481517/122890000000000000000 : ℝ)*(X 1 0+X 2 0)+(2287225785037/1228900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (3523/50000 : ℝ)) (hi := (3867/20000 : ℝ)) (c := (122858576704568481517/122890000000000000000 : ℝ)) (alpha := (2287225785037/1228900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (122858576704568481517/122890000000000000000 : ℝ)*(X 0 1+X 2 1)+(2287225785037/1228900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (3523/50000 : ℝ)) (hi := (3867/20000 : ℝ)) (c := (122858576704568481517/122890000000000000000 : ℝ)) (alpha := (2287225785037/1228900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (122858576704568481517/122890000000000000000 : ℝ)*(X 0 2+X 1 2)+(2287225785037/1228900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2159/512 : ℝ)) (lo := (3523/50000 : ℝ)) (hi := (3867/20000 : ℝ)) (c := (122858576704568481517/122890000000000000000 : ℝ)) (alpha := (2287225785037/1228900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2020201277/10000000000 : ℝ)*X 0 0+(684397759/1250000000 : ℝ)*X 0 1+(1037551031/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5364767363/10000000000 : ℝ)*X 1 0+(-2168580889/10000000000 : ℝ)*X 1 1+(5187755507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2682383709/5000000000 : ℝ)*X 2 0+(5187755439/10000000000 : ℝ)*X 2 1+(-433716181/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((67443501/156250000 : ℝ)*X 0 0+(502909573/1250000000 : ℝ)*X 0 1+(2314582627/5000000000 : ℝ)*X 0 2+(67443501/156250000 : ℝ)*X 1 0+(502909573/1250000000 : ℝ)*X 1 1+(2314582627/5000000000 : ℝ)*X 1 2+(67443501/156250000 : ℝ)*X 2 0+(502909573/1250000000 : ℝ)*X 2 1+(2314582627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-252532809/1250000000 : ℝ)*X 0 0+(5189524773/10000000000 : ℝ)*X 0 1+(5473396791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058109627/2000000000 : ℝ)*X 1 0+(-1882939319/10000000000 : ℝ)*X 1 1+(5473396747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058109621/2000000000 : ℝ)*X 2 0+(1094679359/2000000000 : ℝ)*X 2 1+(-1882939293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863302671/2000000000 : ℝ)*X 0 0+(1156358877/2500000000 : ℝ)*X 0 1+(251689959/625000000 : ℝ)*X 0 2+(863302671/2000000000 : ℝ)*X 1 0+(1156358877/2500000000 : ℝ)*X 1 1+(251689959/625000000 : ℝ)*X 1 2+(863302671/2000000000 : ℝ)*X 2 0+(1156358877/2500000000 : ℝ)*X 2 1+(251689959/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1359_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9992968201289983515363585729/1536125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1063451987/100000000000000 : ℝ)*(base19) + (1070865547/100000000000000 : ℝ)*(base23) + (378957/2500000000000 : ℝ)*(lower2) + (145883033/100000000000000 : ℝ)*(upper3) + (117392647/100000000000000 : ℝ)*(upper5) + (1282415560906279/50000000000000 : ℝ)*(major0) + (1282415560906279/50000000000000 : ℝ)*(major1) + (1282415560906279/50000000000000 : ℝ)*(major2) + (869790612872037/25000000000000 : ℝ)*(sp0) + (13590540954667/390625000000 : ℝ)*(sp1) + (434897309622649/12500000000000 : ℝ)*(sp2) + (825237552908453/50000000000000 : ℝ)*(sp3) + (17096358591/100000000000000 : ℝ)*(sp4) + (57602483/781250000000 : ℝ)*(sp7) + (165048247893473/10000000000000 : ℝ)*(f.failure) + (3479179547846739/100000000000000 : ℝ)*(f.sum) + (164709001448113/30722500000000000000000000000 : ℝ)*base65 + (22303517924564454757/6144500000000000000000000000000000 : ℝ)*base68 + (36548649030031454757/6144500000000000000000000000000000 : ℝ)*base70 + (28238633549246954757/6144500000000000000000000000000000 : ℝ)*base72 + (91106982816557/30722500000000000000000000000 : ℝ)*base74 + (44394037832844954757/6144500000000000000000000000000000 : ℝ)*base76 + (23975341056793045243/6144500000000000000000000000000000 : ℝ)*base77 + (30676909425074954757/6144500000000000000000000000000000 : ℝ)*base80 + (113902575565127/30722500000000000000000000000 : ℝ)*base82 + (457551/100000000000000000000 : ℝ)*base89 + (457551/100000000000000000000 : ℝ)*base91 + (457551/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77889506310623435544303/15361250000000000000000000000 : ℝ) := by norm_num
    linear_combination (277486873/25000000000000 : ℝ)*(base19) + (306615551/25000000000000 : ℝ)*(base23) + (62264169/50000000000000 : ℝ)*(upper3) + (2708329/5000000000000 : ℝ)*(lower4) + (18128371/25000000000000 : ℝ)*(upper5) + (162307703270883/6250000000000 : ℝ)*(major0) + (162307703270883/6250000000000 : ℝ)*(major1) + (162307703270883/6250000000000 : ℝ)*(major2) + (1585909481/12500000000000 : ℝ)*(sp1) + (7559232251/50000000000000 : ℝ)*(sp2) + (880678099976511/25000000000000 : ℝ)*(sp4) + (220168662667669/6250000000000 : ℝ)*(sp5) + (1761348027489669/50000000000000 : ℝ)*(sp6) + (835566967872459/50000000000000 : ℝ)*(sp7) + (835566967872459/50000000000000 : ℝ)*(f.failure) + (880678099976511/25000000000000 : ℝ)*(f.sum) + (39860373395723/30722500000000000000000000000 : ℝ)*base65 + (604827127266619511/768062500000000000000000000000000 : ℝ)*base67 + (1533445231943380489/768062500000000000000000000000000 : ℝ)*base70 + (637308952765244511/768062500000000000000000000000000 : ℝ)*base71 + (913191124251/3840312500000000000000000000 : ℝ)*base73 + (843129071070369511/768062500000000000000000000000000 : ℝ)*base75 + (1372514340579630489/768062500000000000000000000000000 : ℝ)*base78 + (2289939048606130489/768062500000000000000000000000000 : ℝ)*base80 + (17316427709953/7680625000000000000000000000 : ℝ)*base82 + (3272133/500000000000000000000 : ℝ)*base89 + (3272133/500000000000000000000 : ℝ)*base91 + (3272133/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1359_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3867/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3523/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9961/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8019/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1359_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1359_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9961/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8019/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1359_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1359_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1359_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2159/512 : ℝ) ≤ p) (hpb : p ≤ (4319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15539887/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9961/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8019/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1359_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

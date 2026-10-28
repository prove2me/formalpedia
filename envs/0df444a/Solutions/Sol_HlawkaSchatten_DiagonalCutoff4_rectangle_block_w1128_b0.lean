-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1128_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:25:17.341223+00:00
-- url     : https://prove2.me/submissions/be1821af-f750-4b13-b274-9d6c003743f2

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
theorem support_rectangle_w1128_s0_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-237031203/1250000000 : ℝ)*x 0 + (6057571691/10000000000 : ℝ)*x 1 + (95573981/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (237031203/1250000000 : ℝ)^8321 ≤ (11019042893923/100000000000000 : ℝ)^6273 := by
    have hnat : (237031203 : ℕ)^8321*100000000000000^6273 ≤ 11019042893923^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237031203 1250000000 11019042893923 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6057571691/10000000000 : ℝ)^8321 ≤ (51430851087111/100000000000000 : ℝ)^6273 := by
    have hnat : (6057571691 : ℕ)^8321*100000000000000^6273 ≤ 51430851087111^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6057571691 10000000000 51430851087111 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95573981/200000000 : ℝ)^8321 ≤ (9387526500493/25000000000000 : ℝ)^6273 := by
    have hnat : (95573981 : ℕ)^8321*25000000000000^6273 ≤ 9387526500493^6273*200000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95573981 200000000 9387526500493 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-237031203/1250000000 : ℝ), (6057571691/10000000000 : ℝ), (95573981/200000000 : ℝ)] ![(11019042893923/100000000000000 : ℝ), (51430851087111/100000000000000 : ℝ), (9387526500493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-237031203/1250000000 : ℝ)|^8321 ≤ (11019042893923/100000000000000 : ℝ)^6273
        have hw : |(-237031203/1250000000 : ℝ)|=(237031203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6057571691/10000000000 : ℝ)|^8321 ≤ (51430851087111/100000000000000 : ℝ)^6273
        have hw : |(6057571691/10000000000 : ℝ)|=(6057571691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95573981/200000000 : ℝ)|^8321 ≤ (9387526500493/25000000000000 : ℝ)^6273
        have hw : |(95573981/200000000 : ℝ)|=(95573981/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s0_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5517582311/10000000000 : ℝ)*x 0 + (-2630574421/10000000000 : ℝ)*x 1 + (4778699079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517582311/10000000000 : ℝ)^8321 ≤ (45439688738491/100000000000000 : ℝ)^6273 := by
    have hnat : (5517582311 : ℕ)^8321*100000000000000^6273 ≤ 45439688738491^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517582311 10000000000 45439688738491 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630574421/10000000000 : ℝ)^8321 ≤ (2126275617979/12500000000000 : ℝ)^6273 := by
    have hnat : (2630574421 : ℕ)^8321*12500000000000^6273 ≤ 2126275617979^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630574421 10000000000 2126275617979 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4778699079/10000000000 : ℝ)^8321 ≤ (7510021260849/20000000000000 : ℝ)^6273 := by
    have hnat : (4778699079 : ℕ)^8321*20000000000000^6273 ≤ 7510021260849^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4778699079 10000000000 7510021260849 20000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517582311/10000000000 : ℝ), (-2630574421/10000000000 : ℝ), (4778699079/10000000000 : ℝ)] ![(45439688738491/100000000000000 : ℝ), (2126275617979/12500000000000 : ℝ), (7510021260849/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517582311/10000000000 : ℝ)|^8321 ≤ (45439688738491/100000000000000 : ℝ)^6273
        have hw : |(5517582311/10000000000 : ℝ)|=(5517582311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2630574421/10000000000 : ℝ)|^8321 ≤ (2126275617979/12500000000000 : ℝ)^6273
        have hw : |(-2630574421/10000000000 : ℝ)|=(2630574421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4778699079/10000000000 : ℝ)|^8321 ≤ (7510021260849/20000000000000 : ℝ)^6273
        have hw : |(4778699079/10000000000 : ℝ)|=(4778699079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s0_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5517582279/10000000000 : ℝ)*x 0 + (4778699099/10000000000 : ℝ)*x 1 + (-2630574437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517582279/10000000000 : ℝ)^8321 ≤ (45439688388919/100000000000000 : ℝ)^6273 := by
    have hnat : (5517582279 : ℕ)^8321*100000000000000^6273 ≤ 45439688388919^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517582279 10000000000 45439688388919 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4778699099/10000000000 : ℝ)^8321 ≤ (37550106512709/100000000000000 : ℝ)^6273 := by
    have hnat : (4778699099 : ℕ)^8321*100000000000000^6273 ≤ 37550106512709^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4778699099 10000000000 37550106512709 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630574437/10000000000 : ℝ)^8321 ≤ (17010205081071/100000000000000 : ℝ)^6273 := by
    have hnat : (2630574437 : ℕ)^8321*100000000000000^6273 ≤ 17010205081071^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630574437 10000000000 17010205081071 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517582279/10000000000 : ℝ), (4778699099/10000000000 : ℝ), (-2630574437/10000000000 : ℝ)] ![(45439688388919/100000000000000 : ℝ), (37550106512709/100000000000000 : ℝ), (17010205081071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517582279/10000000000 : ℝ)|^8321 ≤ (45439688388919/100000000000000 : ℝ)^6273
        have hw : |(5517582279/10000000000 : ℝ)|=(5517582279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4778699099/10000000000 : ℝ)|^8321 ≤ (37550106512709/100000000000000 : ℝ)^6273
        have hw : |(4778699099/10000000000 : ℝ)|=(4778699099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2630574437/10000000000 : ℝ)|^8321 ≤ (17010205081071/100000000000000 : ℝ)^6273
        have hw : |(-2630574437/10000000000 : ℝ)|=(2630574437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s0_3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (65658211/156250000 : ℝ)*x 0 + (3121735849/10000000000 : ℝ)*x 1 + (353689693/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65658211/156250000 : ℝ)^8321 ≤ (7915525201393/25000000000000 : ℝ)^6273 := by
    have hnat : (65658211 : ℕ)^8321*25000000000000^6273 ≤ 7915525201393^6273*156250000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65658211 156250000 7915525201393 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3121735849/10000000000 : ℝ)^8321 ≤ (21346532353957/100000000000000 : ℝ)^6273 := by
    have hnat : (3121735849 : ℕ)^8321*100000000000000^6273 ≤ 21346532353957^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3121735849 10000000000 21346532353957 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (353689693/625000000 : ℝ)^8321 ≤ (2936960426897/6250000000000 : ℝ)^6273 := by
    have hnat : (353689693 : ℕ)^8321*6250000000000^6273 ≤ 2936960426897^6273*625000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353689693 625000000 2936960426897 6250000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65658211/156250000 : ℝ), (3121735849/10000000000 : ℝ), (353689693/625000000 : ℝ)] ![(7915525201393/25000000000000 : ℝ), (21346532353957/100000000000000 : ℝ), (2936960426897/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65658211/156250000 : ℝ)|^8321 ≤ (7915525201393/25000000000000 : ℝ)^6273
        have hw : |(65658211/156250000 : ℝ)|=(65658211/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3121735849/10000000000 : ℝ)|^8321 ≤ (21346532353957/100000000000000 : ℝ)^6273
        have hw : |(3121735849/10000000000 : ℝ)|=(3121735849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(353689693/625000000 : ℝ)|^8321 ≤ (2936960426897/6250000000000 : ℝ)^6273
        have hw : |(353689693/625000000 : ℝ)|=(353689693/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s0_4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-950718249/5000000000 : ℝ)*x 0 + (4811697153/10000000000 : ℝ)*x 1 + (6023414513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (950718249/5000000000 : ℝ)^8321 ≤ (2764760448639/25000000000000 : ℝ)^6273 := by
    have hnat : (950718249 : ℕ)^8321*25000000000000^6273 ≤ 2764760448639^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950718249 5000000000 2764760448639 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4811697153/10000000000 : ℝ)^8321 ≤ (4736804930459/12500000000000 : ℝ)^6273 := by
    have hnat : (4811697153 : ℕ)^8321*12500000000000^6273 ≤ 4736804930459^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4811697153 10000000000 4736804930459 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6023414513/10000000000 : ℝ)^8321 ≤ (6380814844459/12500000000000 : ℝ)^6273 := by
    have hnat : (6023414513 : ℕ)^8321*12500000000000^6273 ≤ 6380814844459^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6023414513 10000000000 6380814844459 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-950718249/5000000000 : ℝ), (4811697153/10000000000 : ℝ), (6023414513/10000000000 : ℝ)] ![(2764760448639/25000000000000 : ℝ), (4736804930459/12500000000000 : ℝ), (6380814844459/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-950718249/5000000000 : ℝ)|^8321 ≤ (2764760448639/25000000000000 : ℝ)^6273
        have hw : |(-950718249/5000000000 : ℝ)|=(950718249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4811697153/10000000000 : ℝ)|^8321 ≤ (4736804930459/12500000000000 : ℝ)^6273
        have hw : |(4811697153/10000000000 : ℝ)|=(4811697153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6023414513/10000000000 : ℝ)|^8321 ≤ (6380814844459/12500000000000 : ℝ)^6273
        have hw : |(6023414513/10000000000 : ℝ)|=(6023414513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s0_5 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2585076813/5000000000 : ℝ)*x 0 + (-1385859079/10000000000 : ℝ)*x 1 + (1505853609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585076813/5000000000 : ℝ)^8321 ≤ (20841955812187/50000000000000 : ℝ)^6273 := by
    have hnat : (2585076813 : ℕ)^8321*50000000000000^6273 ≤ 20841955812187^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585076813 5000000000 20841955812187 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1385859079/10000000000 : ℝ)^8321 ≤ (1453914092981/20000000000000 : ℝ)^6273 := by
    have hnat : (1385859079 : ℕ)^8321*20000000000000^6273 ≤ 1453914092981^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385859079 10000000000 1453914092981 20000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1505853609/2500000000 : ℝ)^8321 ≤ (25523258945039/50000000000000 : ℝ)^6273 := by
    have hnat : (1505853609 : ℕ)^8321*50000000000000^6273 ≤ 25523258945039^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505853609 2500000000 25523258945039 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585076813/5000000000 : ℝ), (-1385859079/10000000000 : ℝ), (1505853609/2500000000 : ℝ)] ![(20841955812187/50000000000000 : ℝ), (1453914092981/20000000000000 : ℝ), (25523258945039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585076813/5000000000 : ℝ)|^8321 ≤ (20841955812187/50000000000000 : ℝ)^6273
        have hw : |(2585076813/5000000000 : ℝ)|=(2585076813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1385859079/10000000000 : ℝ)|^8321 ≤ (1453914092981/20000000000000 : ℝ)^6273
        have hw : |(-1385859079/10000000000 : ℝ)|=(1385859079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1505853609/2500000000 : ℝ)|^8321 ≤ (25523258945039/50000000000000 : ℝ)^6273
        have hw : |(1505853609/2500000000 : ℝ)|=(1505853609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s0_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1292538413/2500000000 : ℝ)*x 0 + (1505853607/2500000000 : ℝ)*x 1 + (-346464763/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292538413/2500000000 : ℝ)^8321 ≤ (20841955951217/50000000000000 : ℝ)^6273 := by
    have hnat : (1292538413 : ℕ)^8321*50000000000000^6273 ≤ 20841955951217^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292538413 2500000000 20841955951217 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1505853607/2500000000 : ℝ)^8321 ≤ (25523258900073/50000000000000 : ℝ)^6273 := by
    have hnat : (1505853607 : ℕ)^8321*50000000000000^6273 ≤ 25523258900073^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505853607 2500000000 25523258900073 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (346464763/2500000000 : ℝ)^8321 ≤ (7269570277037/100000000000000 : ℝ)^6273 := by
    have hnat : (346464763 : ℕ)^8321*100000000000000^6273 ≤ 7269570277037^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346464763 2500000000 7269570277037 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292538413/2500000000 : ℝ), (1505853607/2500000000 : ℝ), (-346464763/2500000000 : ℝ)] ![(20841955951217/50000000000000 : ℝ), (25523258900073/50000000000000 : ℝ), (7269570277037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292538413/2500000000 : ℝ)|^8321 ≤ (20841955951217/50000000000000 : ℝ)^6273
        have hw : |(1292538413/2500000000 : ℝ)|=(1292538413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1505853607/2500000000 : ℝ)|^8321 ≤ (25523258900073/50000000000000 : ℝ)^6273
        have hw : |(1505853607/2500000000 : ℝ)|=(1505853607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-346464763/2500000000 : ℝ)|^8321 ≤ (7269570277037/100000000000000 : ℝ)^6273
        have hw : |(-346464763/2500000000 : ℝ)|=(346464763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s0_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2106208247/5000000000 : ℝ)*x 0 + (5593566369/10000000000 : ℝ)*x 1 + (1594752139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106208247/5000000000 : ℝ)^8321 ≤ (31764997538951/100000000000000 : ℝ)^6273 := by
    have hnat : (2106208247 : ℕ)^8321*100000000000000^6273 ≤ 31764997538951^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106208247 5000000000 31764997538951 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5593566369/10000000000 : ℝ)^8321 ≤ (46271608524899/100000000000000 : ℝ)^6273 := by
    have hnat : (5593566369 : ℕ)^8321*100000000000000^6273 ≤ 46271608524899^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5593566369 10000000000 46271608524899 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1594752139/5000000000 : ℝ)^8321 ≤ (21963393923907/100000000000000 : ℝ)^6273 := by
    have hnat : (1594752139 : ℕ)^8321*100000000000000^6273 ≤ 21963393923907^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1594752139 5000000000 21963393923907 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2106208247/5000000000 : ℝ), (5593566369/10000000000 : ℝ), (1594752139/5000000000 : ℝ)] ![(31764997538951/100000000000000 : ℝ), (46271608524899/100000000000000 : ℝ), (21963393923907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2106208247/5000000000 : ℝ)|^8321 ≤ (31764997538951/100000000000000 : ℝ)^6273
        have hw : |(2106208247/5000000000 : ℝ)|=(2106208247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5593566369/10000000000 : ℝ)|^8321 ≤ (46271608524899/100000000000000 : ℝ)^6273
        have hw : |(5593566369/10000000000 : ℝ)|=(5593566369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1594752139/5000000000 : ℝ)|^8321 ≤ (21963393923907/100000000000000 : ℝ)^6273
        have hw : |(1594752139/5000000000 : ℝ)|=(1594752139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1128_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (89/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27869/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (65/16 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^65 ≤ (0 : ℝ)^16 := by
      have hnat : (0 : ℕ)^65*1^16 ≤ 0^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (65/16 : ℝ) ≤ (2417512424541155547/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^65 ≤ (2417512424541155547/100000000000000000000 : ℝ)^16 := by
      have hnat : (2 : ℕ)^65*100000000000000000000^16 ≤ 2417512424541155547^16*5^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2417512424541155547 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2417512424541155547/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (1 : ℝ)^16 ≤ (1 : ℝ)^65 := by
      have hnat : (1 : ℕ)^16*1^65 ≤ 1^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (102417512424541155547/100000000000000000000 : ℝ) ≤ (10058973289982177/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (102417512424541155547/100000000000000000000 : ℝ)^16 ≤ (10058973289982177/10000000000000000 : ℝ)^65 := by
      have hnat : (102417512424541155547 : ℕ)^16*10000000000000000^65 ≤ 10058973289982177^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102417512424541155547 100000000000000000000 10058973289982177 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10058973289982177/10000000000000000 : ℝ)) (X := (102417512424541155547/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (52417512424541155547/50000000000000000000 : ℝ) ≤ (5058973289982177/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (52417512424541155547/50000000000000000000 : ℝ)^16 ≤ (5058973289982177/5000000000000000 : ℝ)^65 := by
      have hnat : (52417512424541155547 : ℕ)^16*5000000000000000^65 ≤ 5058973289982177^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52417512424541155547 50000000000000000000 5058973289982177 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5058973289982177/5000000000000000 : ℝ)) (X := (52417512424541155547/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(58973289982177/4000000000000000 : ℝ)*(0 : ℝ))^(65/16 : ℝ) := by
    rw [show (1 : ℝ)+2*(58973289982177/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2417512424541155547/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(58973289982177/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(65/16 : ℝ) := by
    rw [show (1 : ℝ)+(58973289982177/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10058973289982177/10000000000000000 : ℝ) by norm_num, show 1+(2417512424541155547/100000000000000000000 : ℝ)+(0 : ℝ)=(102417512424541155547/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2417512424541155547/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(58973289982177/4000000000000000 : ℝ)*(2/5 : ℝ))^(65/16 : ℝ) := by
    rw [show (1 : ℝ)+2*(58973289982177/4000000000000000 : ℝ)*(2/5 : ℝ)=(5058973289982177/5000000000000000 : ℝ) by norm_num, show 1+2*(2417512424541155547/100000000000000000000 : ℝ)=(52417512424541155547/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(58973289982177/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58973289982177/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(58973289982177/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58973289982177/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(58973289982177/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58973289982177/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-237031203/1250000000 : ℝ)*X 0 0+(6057571691/10000000000 : ℝ)*X 0 1+(95573981/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5517582311/10000000000 : ℝ)*X 1 0+(-2630574421/10000000000 : ℝ)*X 1 1+(4778699079/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5517582279/10000000000 : ℝ)*X 2 0+(4778699099/10000000000 : ℝ)*X 2 1+(-2630574437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((65658211/156250000 : ℝ)*X 0 0+(3121735849/10000000000 : ℝ)*X 0 1+(353689693/625000000 : ℝ)*X 0 2+(65658211/156250000 : ℝ)*X 1 0+(3121735849/10000000000 : ℝ)*X 1 1+(353689693/625000000 : ℝ)*X 1 2+(65658211/156250000 : ℝ)*X 2 0+(3121735849/10000000000 : ℝ)*X 2 1+(353689693/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-950718249/5000000000 : ℝ)*X 0 0+(4811697153/10000000000 : ℝ)*X 0 1+(6023414513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2585076813/5000000000 : ℝ)*X 1 0+(-1385859079/10000000000 : ℝ)*X 1 1+(1505853609/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1292538413/2500000000 : ℝ)*X 2 0+(1505853607/2500000000 : ℝ)*X 2 1+(-346464763/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2106208247/5000000000 : ℝ)*X 0 0+(5593566369/10000000000 : ℝ)*X 0 1+(1594752139/5000000000 : ℝ)*X 0 2+(2106208247/5000000000 : ℝ)*X 1 0+(5593566369/10000000000 : ℝ)*X 1 1+(1594752139/5000000000 : ℝ)*X 1 2+(2106208247/5000000000 : ℝ)*X 2 0+(5593566369/10000000000 : ℝ)*X 2 1+(1594752139/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10987896516937627122843/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14664501/50000000000000 : ℝ)*(base1) + (69099997/10000000000000 : ℝ)*(base19) + (640372111/100000000000000 : ℝ)*(base23) + (46092877/100000000000000 : ℝ)*(base24) + (79528157/50000000000000 : ℝ)*(upper3) + (11760644207753/2000000000000 : ℝ)*(major0) + (11760644207753/2000000000000 : ℝ)*(major1) + (11760644207753/2000000000000 : ℝ)*(major2) + (195485253778563/25000000000000 : ℝ)*(sp0) + (390970910570069/50000000000000 : ℝ)*(sp1) + (781941825675121/100000000000000 : ℝ)*(sp2) + (394120569998893/100000000000000 : ℝ)*(sp3) + (1526354859/100000000000000 : ℝ)*(sp4) + (1217741483/100000000000000 : ℝ)*(sp7) + (394121817069377/100000000000000 : ℝ)*(f.failure) + (195485628035027/25000000000000 : ℝ)*(f.sum) + (1924355357719/4000000000000000000000000000 : ℝ)*base66 + (37462400325719/8000000000000000000000000000 : ℝ)*base68 + (15977646218281/8000000000000000000000000000 : ℝ)*base69 + (26154162482281/8000000000000000000000000000 : ℝ)*base71 + (10181105925719/4000000000000000000000000000 : ℝ)*base74 + (25353617138281/8000000000000000000000000000 : ℝ)*base75 + (2324892245719/8000000000000000000000000000 : ℝ)*base78 + (39266875685719/8000000000000000000000000000 : ℝ)*base80 + (21694695294281/4000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (6269297/625000000000000000000 : ℝ)*base90 + (6269297/625000000000000000000 : ℝ)*base92 + (6269297/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10121947742918341811589/1600000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38533859/50000000000000 : ℝ)*(base1) + (1556643409/100000000000000 : ℝ)*(base19) + (1560139143/100000000000000 : ℝ)*(base23) + (17125049/10000000000000 : ℝ)*(upper3) + (45257171/25000000000000 : ℝ)*(upper5) + (24824756975881/4000000000000 : ℝ)*(major0) + (24824756975881/4000000000000 : ℝ)*(major1) + (24824756975881/4000000000000 : ℝ)*(major2) + (3173306897/100000000000000 : ℝ)*(sp1) + (3163568387/100000000000000 : ℝ)*(sp2) + (825275028131379/100000000000000 : ℝ)*(sp4) + (165054044222671/20000000000000 : ℝ)*(sp5) + (82527022735613/10000000000000 : ℝ)*(sp6) + (103990652447189/25000000000000 : ℝ)*(sp7) + (207981343428237/50000000000000 : ℝ)*(f.failure) + (825274951063661/100000000000000 : ℝ)*(f.sum) + (14691143096937/8000000000000000000000000000 : ℝ)*base65 + (90428466343063/16000000000000000000000000000 : ℝ)*base68 + (61933283352937/16000000000000000000000000000 : ℝ)*base69 + (53544258296937/16000000000000000000000000000 : ℝ)*base71 + (5495186616937/8000000000000000000000000000 : ℝ)*base73 + (77319887896937/16000000000000000000000000000 : ℝ)*base75 + (54054233720937/16000000000000000000000000000 : ℝ)*base77 + (20391326200937/16000000000000000000000000000 : ℝ)*base79 + (722218560937/8000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (601243/312500000000000000000 : ℝ)*base89 + (601243/312500000000000000000 : ℝ)*base91 + (601243/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1128_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (89/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27869/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1128_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1128_s1_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050961619/5000000000 : ℝ)*x 0 + (2852634273/5000000000 : ℝ)*x 1 + (1249831139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050961619/5000000000 : ℝ)^8321 ≤ (6315907804223/50000000000000 : ℝ)^6273 := by
    have hnat : (1050961619 : ℕ)^8321*50000000000000^6273 ≤ 6315907804223^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050961619 5000000000 6315907804223 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2852634273/5000000000 : ℝ)^8321 ≤ (23750648115191/50000000000000 : ℝ)^6273 := by
    have hnat : (2852634273 : ℕ)^8321*50000000000000^6273 ≤ 23750648115191^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2852634273 5000000000 23750648115191 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1249831139/2500000000 : ℝ)^8321 ≤ (3986688814501/10000000000000 : ℝ)^6273 := by
    have hnat : (1249831139 : ℕ)^8321*10000000000000^6273 ≤ 3986688814501^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249831139 2500000000 3986688814501 10000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050961619/5000000000 : ℝ), (2852634273/5000000000 : ℝ), (1249831139/2500000000 : ℝ)] ![(6315907804223/50000000000000 : ℝ), (23750648115191/50000000000000 : ℝ), (3986688814501/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050961619/5000000000 : ℝ)|^8321 ≤ (6315907804223/50000000000000 : ℝ)^6273
        have hw : |(-1050961619/5000000000 : ℝ)|=(1050961619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2852634273/5000000000 : ℝ)|^8321 ≤ (23750648115191/50000000000000 : ℝ)^6273
        have hw : |(2852634273/5000000000 : ℝ)|=(2852634273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1249831139/2500000000 : ℝ)|^8321 ≤ (3986688814501/10000000000000 : ℝ)^6273
        have hw : |(1249831139/2500000000 : ℝ)|=(1249831139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s1_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2709946589/5000000000 : ℝ)*x 0 + (-2483162497/10000000000 : ℝ)*x 1 + (499932417/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709946589/5000000000 : ℝ)^8321 ≤ (44375616831947/100000000000000 : ℝ)^6273 := by
    have hnat : (2709946589 : ℕ)^8321*100000000000000^6273 ≤ 44375616831947^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709946589 5000000000 44375616831947 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2483162497/10000000000 : ℝ)^8321 ≤ (15757499087373/100000000000000 : ℝ)^6273 := by
    have hnat : (2483162497 : ℕ)^8321*100000000000000^6273 ≤ 15757499087373^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2483162497 10000000000 15757499087373 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499932417/1000000000 : ℝ)^8321 ≤ (9966721015481/25000000000000 : ℝ)^6273 := by
    have hnat : (499932417 : ℕ)^8321*25000000000000^6273 ≤ 9966721015481^6273*1000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499932417 1000000000 9966721015481 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709946589/5000000000 : ℝ), (-2483162497/10000000000 : ℝ), (499932417/1000000000 : ℝ)] ![(44375616831947/100000000000000 : ℝ), (15757499087373/100000000000000 : ℝ), (9966721015481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709946589/5000000000 : ℝ)|^8321 ≤ (44375616831947/100000000000000 : ℝ)^6273
        have hw : |(2709946589/5000000000 : ℝ)|=(2709946589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2483162497/10000000000 : ℝ)|^8321 ≤ (15757499087373/100000000000000 : ℝ)^6273
        have hw : |(-2483162497/10000000000 : ℝ)|=(2483162497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(499932417/1000000000 : ℝ)|^8321 ≤ (9966721015481/25000000000000 : ℝ)^6273
        have hw : |(499932417/1000000000 : ℝ)|=(499932417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s1_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1083978971/2000000000 : ℝ)*x 0 + (156228833/312500000 : ℝ)*x 1 + (-620790559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083978971/2000000000 : ℝ)^8321 ≤ (22187817522589/50000000000000 : ℝ)^6273 := by
    have hnat : (1083978971 : ℕ)^8321*50000000000000^6273 ≤ 22187817522589^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083978971 2000000000 22187817522589 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156228833/312500000 : ℝ)^8321 ≤ (39866868046919/100000000000000 : ℝ)^6273 := by
    have hnat : (156228833 : ℕ)^8321*100000000000000^6273 ≤ 39866868046919^6273*312500000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156228833 312500000 39866868046919 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (620790559/2500000000 : ℝ)^8321 ≤ (1575749689041/10000000000000 : ℝ)^6273 := by
    have hnat : (620790559 : ℕ)^8321*10000000000000^6273 ≤ 1575749689041^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620790559 2500000000 1575749689041 10000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083978971/2000000000 : ℝ), (156228833/312500000 : ℝ), (-620790559/2500000000 : ℝ)] ![(22187817522589/50000000000000 : ℝ), (39866868046919/100000000000000 : ℝ), (1575749689041/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083978971/2000000000 : ℝ)|^8321 ≤ (22187817522589/50000000000000 : ℝ)^6273
        have hw : |(1083978971/2000000000 : ℝ)|=(1083978971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156228833/312500000 : ℝ)|^8321 ≤ (39866868046919/100000000000000 : ℝ)^6273
        have hw : |(156228833/312500000 : ℝ)|=(156228833/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-620790559/2500000000 : ℝ)|^8321 ≤ (1575749689041/10000000000000 : ℝ)^6273
        have hw : |(-620790559/2500000000 : ℝ)|=(620790559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s1_3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4318621393/10000000000 : ℝ)*x 0 + (3674399659/10000000000 : ℝ)*x 1 + (2537499667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318621393/10000000000 : ℝ)^8321 ≤ (16415841123251/50000000000000 : ℝ)^6273 := by
    have hnat : (4318621393 : ℕ)^8321*50000000000000^6273 ≤ 16415841123251^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318621393 10000000000 16415841123251 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3674399659/10000000000 : ℝ)^8321 ≤ (2649897479129/10000000000000 : ℝ)^6273 := by
    have hnat : (3674399659 : ℕ)^8321*10000000000000^6273 ≤ 2649897479129^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3674399659 10000000000 2649897479129 10000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2537499667/5000000000 : ℝ)^8321 ≤ (20334671471633/50000000000000 : ℝ)^6273 := by
    have hnat : (2537499667 : ℕ)^8321*50000000000000^6273 ≤ 20334671471633^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537499667 5000000000 20334671471633 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318621393/10000000000 : ℝ), (3674399659/10000000000 : ℝ), (2537499667/5000000000 : ℝ)] ![(16415841123251/50000000000000 : ℝ), (2649897479129/10000000000000 : ℝ), (20334671471633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318621393/10000000000 : ℝ)|^8321 ≤ (16415841123251/50000000000000 : ℝ)^6273
        have hw : |(4318621393/10000000000 : ℝ)|=(4318621393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3674399659/10000000000 : ℝ)|^8321 ≤ (2649897479129/10000000000000 : ℝ)^6273
        have hw : |(3674399659/10000000000 : ℝ)|=(3674399659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2537499667/5000000000 : ℝ)|^8321 ≤ (20334671471633/50000000000000 : ℝ)^6273
        have hw : |(2537499667/5000000000 : ℝ)|=(2537499667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s1_4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2102749279/10000000000 : ℝ)*x 0 + (626126907/1250000000 : ℝ)*x 1 + (1423846213/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102749279/10000000000 : ℝ)^8321 ≤ (6319200477401/50000000000000 : ℝ)^6273 := by
    have hnat : (2102749279 : ℕ)^8321*50000000000000^6273 ≤ 6319200477401^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102749279 10000000000 6319200477401 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626126907/1250000000 : ℝ)^8321 ≤ (39969428243109/100000000000000 : ℝ)^6273 := by
    have hnat : (626126907 : ℕ)^8321*100000000000000^6273 ≤ 39969428243109^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626126907 1250000000 39969428243109 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1423846213/2500000000 : ℝ)^8321 ≤ (11848042697159/25000000000000 : ℝ)^6273 := by
    have hnat : (1423846213 : ℕ)^8321*25000000000000^6273 ≤ 11848042697159^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423846213 2500000000 11848042697159 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2102749279/10000000000 : ℝ), (626126907/1250000000 : ℝ), (1423846213/2500000000 : ℝ)] ![(6319200477401/50000000000000 : ℝ), (39969428243109/100000000000000 : ℝ), (11848042697159/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2102749279/10000000000 : ℝ)|^8321 ≤ (6319200477401/50000000000000 : ℝ)^6273
        have hw : |(-2102749279/10000000000 : ℝ)|=(2102749279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(626126907/1250000000 : ℝ)|^8321 ≤ (39969428243109/100000000000000 : ℝ)^6273
        have hw : |(626126907/1250000000 : ℝ)|=(626126907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1423846213/2500000000 : ℝ)|^8321 ≤ (11848042697159/25000000000000 : ℝ)^6273
        have hw : |(1423846213/2500000000 : ℝ)|=(1423846213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s1_5 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1309757303/2500000000 : ℝ)*x 0 + (-446775363/2500000000 : ℝ)*x 1 + (5695384597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309757303/2500000000 : ℝ)^8321 ≤ (42422106734219/100000000000000 : ℝ)^6273 := by
    have hnat : (1309757303 : ℕ)^8321*100000000000000^6273 ≤ 42422106734219^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309757303 2500000000 42422106734219 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (446775363/2500000000 : ℝ)^8321 ≤ (5092862641393/50000000000000 : ℝ)^6273 := by
    have hnat : (446775363 : ℕ)^8321*50000000000000^6273 ≤ 5092862641393^6273*2500000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446775363 2500000000 5092862641393 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5695384597/10000000000 : ℝ)^8321 ≤ (47392167973989/100000000000000 : ℝ)^6273 := by
    have hnat : (5695384597 : ℕ)^8321*100000000000000^6273 ≤ 47392167973989^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5695384597 10000000000 47392167973989 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309757303/2500000000 : ℝ), (-446775363/2500000000 : ℝ), (5695384597/10000000000 : ℝ)] ![(42422106734219/100000000000000 : ℝ), (5092862641393/50000000000000 : ℝ), (47392167973989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309757303/2500000000 : ℝ)|^8321 ≤ (42422106734219/100000000000000 : ℝ)^6273
        have hw : |(1309757303/2500000000 : ℝ)|=(1309757303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-446775363/2500000000 : ℝ)|^8321 ≤ (5092862641393/50000000000000 : ℝ)^6273
        have hw : |(-446775363/2500000000 : ℝ)|=(446775363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5695384597/10000000000 : ℝ)|^8321 ≤ (47392167973989/100000000000000 : ℝ)^6273
        have hw : |(5695384597/10000000000 : ℝ)|=(5695384597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s1_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2619514627/5000000000 : ℝ)*x 0 + (2847692383/5000000000 : ℝ)*x 1 + (-357420229/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2619514627/5000000000 : ℝ)^8321 ≤ (21211053592669/50000000000000 : ℝ)^6273 := by
    have hnat : (2619514627 : ℕ)^8321*50000000000000^6273 ≤ 21211053592669^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619514627 5000000000 21211053592669 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2847692383/5000000000 : ℝ)^8321 ≤ (47392169839383/100000000000000 : ℝ)^6273 := by
    have hnat : (2847692383 : ℕ)^8321*100000000000000^6273 ≤ 47392169839383^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2847692383 5000000000 47392169839383 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (357420229/2000000000 : ℝ)^8321 ≤ (10185722961753/100000000000000 : ℝ)^6273 := by
    have hnat : (357420229 : ℕ)^8321*100000000000000^6273 ≤ 10185722961753^6273*2000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357420229 2000000000 10185722961753 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2619514627/5000000000 : ℝ), (2847692383/5000000000 : ℝ), (-357420229/2000000000 : ℝ)] ![(21211053592669/50000000000000 : ℝ), (47392169839383/100000000000000 : ℝ), (10185722961753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2619514627/5000000000 : ℝ)|^8321 ≤ (21211053592669/50000000000000 : ℝ)^6273
        have hw : |(2619514627/5000000000 : ℝ)|=(2619514627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2847692383/5000000000 : ℝ)|^8321 ≤ (47392169839383/100000000000000 : ℝ)^6273
        have hw : |(2847692383/5000000000 : ℝ)|=(2847692383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-357420229/2000000000 : ℝ)|^8321 ≤ (10185722961753/100000000000000 : ℝ)^6273
        have hw : |(-357420229/2000000000 : ℝ)|=(357420229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s1_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2160128719/5000000000 : ℝ)*x 0 + (631971713/1250000000 : ℝ)*x 1 + (3694007957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160128719/5000000000 : ℝ)^8321 ≤ (6569636345911/20000000000000 : ℝ)^6273 := by
    have hnat : (2160128719 : ℕ)^8321*20000000000000^6273 ≤ 6569636345911^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160128719 5000000000 6569636345911 20000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (631971713/1250000000 : ℝ)^8321 ≤ (20232550930931/50000000000000 : ℝ)^6273 := by
    have hnat : (631971713 : ℕ)^8321*50000000000000^6273 ≤ 20232550930931^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631971713 1250000000 20232550930931 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3694007957/10000000000 : ℝ)^8321 ≤ (26686716393193/100000000000000 : ℝ)^6273 := by
    have hnat : (3694007957 : ℕ)^8321*100000000000000^6273 ≤ 26686716393193^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3694007957 10000000000 26686716393193 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160128719/5000000000 : ℝ), (631971713/1250000000 : ℝ), (3694007957/10000000000 : ℝ)] ![(6569636345911/20000000000000 : ℝ), (20232550930931/50000000000000 : ℝ), (26686716393193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160128719/5000000000 : ℝ)|^8321 ≤ (6569636345911/20000000000000 : ℝ)^6273
        have hw : |(2160128719/5000000000 : ℝ)|=(2160128719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(631971713/1250000000 : ℝ)|^8321 ≤ (20232550930931/50000000000000 : ℝ)^6273
        have hw : |(631971713/1250000000 : ℝ)|=(631971713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3694007957/10000000000 : ℝ)|^8321 ≤ (26686716393193/100000000000000 : ℝ)^6273
        have hw : |(3694007957/10000000000 : ℝ)|=(3694007957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1128_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27869/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5571/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20501/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27869/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (89/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27869/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (89/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27869/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (89/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27869/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (89/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27869/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (89/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27869/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (89/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (89/25000 : ℝ) ^ (65/16 : ℝ) ≤ (11291863427/100000000000000000000 : ℝ) := by
    have hpowers : (89/25000 : ℝ)^65 ≤ (11291863427/100000000000000000000 : ℝ)^16 := by
      have hnat : (89 : ℕ)^65*100000000000000000000^16 ≤ 11291863427^16*25000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 25000 11291863427 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/25000 : ℝ)) (X := (11291863427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hpowhi : (27869/100000 : ℝ) ^ (65/16 : ℝ) ≤ (556936432862881191/100000000000000000000 : ℝ) := by
    have hpowers : (27869/100000 : ℝ)^65 ≤ (556936432862881191/100000000000000000000 : ℝ)^16 := by
      have hnat : (27869 : ℕ)^65*100000000000000000000^16 ≤ 556936432862881191^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27869 100000 556936432862881191 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27869/100000 : ℝ)) (X := (556936432862881191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000011291863427/50000000000000000000 : ℝ) ≤ (2500000000138977/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50000000011291863427/50000000000000000000 : ℝ)^16 ≤ (2500000000138977/2500000000000000 : ℝ)^65 := by
      have hnat : (50000000011291863427 : ℕ)^16*2500000000000000^65 ≤ 2500000000138977^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000011291863427 50000000000000000000 2500000000138977 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000000138977/2500000000000000 : ℝ)) (X := (50000000011291863427/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (50278468222077372309/50000000000000000000 : ℝ) ≤ (10013680519458877/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50278468222077372309/50000000000000000000 : ℝ)^16 ≤ (10013680519458877/10000000000000000 : ℝ)^65 := by
      have hnat : (50278468222077372309 : ℕ)^16*10000000000000000^65 ≤ 10013680519458877^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50278468222077372309 50000000000000000000 10013680519458877 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013680519458877/10000000000000000 : ℝ)) (X := (50278468222077372309/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (50556936432862881191/50000000000000000000 : ℝ) ≤ (5013680519180923/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50556936432862881191/50000000000000000000 : ℝ)^16 ≤ (5013680519180923/5000000000000000 : ℝ)^65 := by
      have hnat : (50556936432862881191 : ℕ)^16*5000000000000000^65 ≤ 5013680519180923^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50556936432862881191 50000000000000000000 5013680519180923 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013680519180923/5000000000000000 : ℝ)) (X := (50556936432862881191/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(11291863427/100000000000000000000 : ℝ) ≤ ((68780064871458945719/68782500000000000000 : ℝ)+2*(13680518902969/2751300000000000 : ℝ)*(89/25000 : ℝ))^(65/16 : ℝ) := by
    rw [show (68780064871458945719/68782500000000000000 : ℝ)+2*(13680518902969/2751300000000000 : ℝ)*(89/25000 : ℝ)=(2500000000138977/2500000000000000 : ℝ) by norm_num, show 1+2*(11291863427/100000000000000000000 : ℝ)=(50000000011291863427/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(556936432862881191/100000000000000000000 : ℝ)+(11291863427/100000000000000000000 : ℝ) ≤ ((68780064871458945719/68782500000000000000 : ℝ)+(13680518902969/2751300000000000 : ℝ)*((27869/100000 : ℝ)+(89/25000 : ℝ)))^(65/16 : ℝ) := by
    rw [show (68780064871458945719/68782500000000000000 : ℝ)+(13680518902969/2751300000000000 : ℝ)*((27869/100000 : ℝ)+(89/25000 : ℝ))=(10013680519458877/10000000000000000 : ℝ) by norm_num, show 1+(556936432862881191/100000000000000000000 : ℝ)+(11291863427/100000000000000000000 : ℝ)=(50278468222077372309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(556936432862881191/100000000000000000000 : ℝ) ≤ ((68780064871458945719/68782500000000000000 : ℝ)+2*(13680518902969/2751300000000000 : ℝ)*(27869/100000 : ℝ))^(65/16 : ℝ) := by
    rw [show (68780064871458945719/68782500000000000000 : ℝ)+2*(13680518902969/2751300000000000 : ℝ)*(27869/100000 : ℝ)=(5013680519180923/5000000000000000 : ℝ) by norm_num, show 1+2*(556936432862881191/100000000000000000000 : ℝ)=(50556936432862881191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (68780064871458945719/68782500000000000000 : ℝ)*(X 1 0+X 2 0)+(13680518902969/2751300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (89/25000 : ℝ)) (hi := (27869/100000 : ℝ)) (c := (68780064871458945719/68782500000000000000 : ℝ)) (alpha := (13680518902969/2751300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (68780064871458945719/68782500000000000000 : ℝ)*(X 0 1+X 2 1)+(13680518902969/2751300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (89/25000 : ℝ)) (hi := (27869/100000 : ℝ)) (c := (68780064871458945719/68782500000000000000 : ℝ)) (alpha := (13680518902969/2751300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (68780064871458945719/68782500000000000000 : ℝ)*(X 0 2+X 1 2)+(13680518902969/2751300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (89/25000 : ℝ)) (hi := (27869/100000 : ℝ)) (c := (68780064871458945719/68782500000000000000 : ℝ)) (alpha := (13680518902969/2751300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1050961619/5000000000 : ℝ)*X 0 0+(2852634273/5000000000 : ℝ)*X 0 1+(1249831139/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2709946589/5000000000 : ℝ)*X 1 0+(-2483162497/10000000000 : ℝ)*X 1 1+(499932417/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1083978971/2000000000 : ℝ)*X 2 0+(156228833/312500000 : ℝ)*X 2 1+(-620790559/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4318621393/10000000000 : ℝ)*X 0 0+(3674399659/10000000000 : ℝ)*X 0 1+(2537499667/5000000000 : ℝ)*X 0 2+(4318621393/10000000000 : ℝ)*X 1 0+(3674399659/10000000000 : ℝ)*X 1 1+(2537499667/5000000000 : ℝ)*X 1 2+(4318621393/10000000000 : ℝ)*X 2 0+(3674399659/10000000000 : ℝ)*X 2 1+(2537499667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2102749279/10000000000 : ℝ)*X 0 0+(626126907/1250000000 : ℝ)*X 0 1+(1423846213/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1309757303/2500000000 : ℝ)*X 1 0+(-446775363/2500000000 : ℝ)*X 1 1+(5695384597/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2619514627/5000000000 : ℝ)*X 2 0+(2847692383/5000000000 : ℝ)*X 2 1+(-357420229/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2160128719/5000000000 : ℝ)*X 0 0+(631971713/1250000000 : ℝ)*X 0 1+(3694007957/10000000000 : ℝ)*X 0 2+(2160128719/5000000000 : ℝ)*X 1 0+(631971713/1250000000 : ℝ)*X 1 1+(3694007957/10000000000 : ℝ)*X 1 2+(2160128719/5000000000 : ℝ)*X 2 0+(631971713/1250000000 : ℝ)*X 2 1+(3694007957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2187572263586726632648555669/573187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7112729/2000000000000 : ℝ)*(base1) + (29419541/6250000000000 : ℝ)*(base19) + (120465291/12500000000000 : ℝ)*(base23) + (14215747/100000000000000 : ℝ)*(base37) + (12741889/25000000000000 : ℝ)*(upper3) + (532630912107017/50000000000000 : ℝ)*(major0) + (532630912107017/50000000000000 : ℝ)*(major1) + (532630912107017/50000000000000 : ℝ)*(major2) + (1416543457918249/100000000000000 : ℝ)*(sp0) + (7082709706119/500000000000 : ℝ)*(sp1) + (1416543087661769/100000000000000 : ℝ)*(sp2) + (11155923437109/1562500000000 : ℝ)*(sp3) + (474551149/50000000000000 : ℝ)*(sp4) + (1639447641/100000000000000 : ℝ)*(sp5) + (713979469827173/100000000000000 : ℝ)*(f.failure) + (1416544051384097/100000000000000 : ℝ)*(f.sum) + (13856195943143/68782500000000000000000000000 : ℝ)*base65 + (7570881153712753/382125000000000000000000000000000 : ℝ)*base68 + (4118544578051962753/382125000000000000000000000000000 : ℝ)*base70 + (1039575652370962753/382125000000000000000000000000000 : ℝ)*base72 + (86361088738283/68782500000000000000000000000 : ℝ)*base73 + (3722976167203087753/382125000000000000000000000000000 : ℝ)*base76 + (1975236687567337753/382125000000000000000000000000000 : ℝ)*base78 + (1910929476985462753/382125000000000000000000000000000 : ℝ)*base80 + (582540514432777/68782500000000000000000000000 : ℝ)*base82 + (1015253/625000000000000000000 : ℝ)*base90 + (1015253/625000000000000000000 : ℝ)*base92 + (1015253/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (373440248498665288309253331/63687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36567691/50000000000000 : ℝ)*(base1) + (654669141/50000000000000 : ℝ)*(base19) + (1341920787/100000000000000 : ℝ)*(base23) + (15449933/12500000000000 : ℝ)*(upper3) + (130413471/100000000000000 : ℝ)*(upper5) + (547820510130153/50000000000000 : ℝ)*(major0) + (547820510130153/50000000000000 : ℝ)*(major1) + (547820510130153/50000000000000 : ℝ)*(major2) + (518941867/10000000000000 : ℝ)*(sp1) + (2897422347/50000000000000 : ℝ)*(sp2) + (1456941142079601/100000000000000 : ℝ)*(sp4) + (1456934570187267/100000000000000 : ℝ)*(sp5) + (728466966089369/50000000000000 : ℝ)*(sp6) + (73434070298651/10000000000000 : ℝ)*(sp7) + (183585194030473/25000000000000 : ℝ)*(f.failure) + (1456941068944219/100000000000000 : ℝ)*(f.sum) + (11497264069613/5095000000000000000000000000 : ℝ)*base66 + (723053656439910741/127375000000000000000000000000000 : ℝ)*base67 + (938465387403160741/127375000000000000000000000000000 : ℝ)*base69 + (493152946113410741/127375000000000000000000000000000 : ℝ)*base71 + (814847808053/1273750000000000000000000000 : ℝ)*base73 + (716326412941535741/127375000000000000000000000000000 : ℝ)*base75 + (565607163213160741/127375000000000000000000000000000 : ℝ)*base77 + (298321755114410741/127375000000000000000000000000000 : ℝ)*base79 + (336788187119/2547500000000000000000000000 : ℝ)*base82 + (211553/156250000000000000000 : ℝ)*base90 + (211553/156250000000000000000 : ℝ)*base92 + (211553/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1128_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27869/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5571/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20501/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1128_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1128_s2_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2155913139/10000000000 : ℝ)*x 0 + (2756746797/5000000000 : ℝ)*x 1 + (2578391209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155913139/10000000000 : ℝ)^8321 ≤ (6531999720223/50000000000000 : ℝ)^6273 := by
    have hnat : (2155913139 : ℕ)^8321*50000000000000^6273 ≤ 6531999720223^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155913139 10000000000 6531999720223 50000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2756746797/5000000000 : ℝ)^8321 ≤ (45395028476461/100000000000000 : ℝ)^6273 := by
    have hnat : (2756746797 : ℕ)^8321*100000000000000^6273 ≤ 45395028476461^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756746797 5000000000 45395028476461 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2578391209/5000000000 : ℝ)^8321 ≤ (5192621509551/12500000000000 : ℝ)^6273 := by
    have hnat : (2578391209 : ℕ)^8321*12500000000000^6273 ≤ 5192621509551^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2578391209 5000000000 5192621509551 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2155913139/10000000000 : ℝ), (2756746797/5000000000 : ℝ), (2578391209/5000000000 : ℝ)] ![(6531999720223/50000000000000 : ℝ), (45395028476461/100000000000000 : ℝ), (5192621509551/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2155913139/10000000000 : ℝ)|^8321 ≤ (6531999720223/50000000000000 : ℝ)^6273
        have hw : |(-2155913139/10000000000 : ℝ)|=(2155913139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2756746797/5000000000 : ℝ)|^8321 ≤ (45395028476461/100000000000000 : ℝ)^6273
        have hw : |(2756746797/5000000000 : ℝ)|=(2756746797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2578391209/5000000000 : ℝ)|^8321 ≤ (5192621509551/12500000000000 : ℝ)^6273
        have hw : |(2578391209/5000000000 : ℝ)|=(2578391209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s2_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5374468413/10000000000 : ℝ)*x 0 + (-1170734849/5000000000 : ℝ)*x 1 + (5156784081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374468413/10000000000 : ℝ)^8321 ≤ (10970738188033/25000000000000 : ℝ)^6273 := by
    have hnat : (5374468413 : ℕ)^8321*25000000000000^6273 ≤ 10970738188033^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374468413 10000000000 10970738188033 25000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1170734849/5000000000 : ℝ)^8321 ≤ (911003586721/6250000000000 : ℝ)^6273 := by
    have hnat : (1170734849 : ℕ)^8321*6250000000000^6273 ≤ 911003586721^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170734849 5000000000 911003586721 6250000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5156784081/10000000000 : ℝ)^8321 ≤ (41540989846527/100000000000000 : ℝ)^6273 := by
    have hnat : (5156784081 : ℕ)^8321*100000000000000^6273 ≤ 41540989846527^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5156784081 10000000000 41540989846527 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374468413/10000000000 : ℝ), (-1170734849/5000000000 : ℝ), (5156784081/10000000000 : ℝ)] ![(10970738188033/25000000000000 : ℝ), (911003586721/6250000000000 : ℝ), (41540989846527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374468413/10000000000 : ℝ)|^8321 ≤ (10970738188033/25000000000000 : ℝ)^6273
        have hw : |(5374468413/10000000000 : ℝ)|=(5374468413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1170734849/5000000000 : ℝ)|^8321 ≤ (911003586721/6250000000000 : ℝ)^6273
        have hw : |(-1170734849/5000000000 : ℝ)|=(1170734849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5156784081/10000000000 : ℝ)|^8321 ≤ (41540989846527/100000000000000 : ℝ)^6273
        have hw : |(5156784081/10000000000 : ℝ)|=(5156784081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s2_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5374468337/10000000000 : ℝ)*x 0 + (644598013/1250000000 : ℝ)*x 1 + (-292683721/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374468337/10000000000 : ℝ)^8321 ≤ (43882951928991/100000000000000 : ℝ)^6273 := by
    have hnat : (5374468337 : ℕ)^8321*100000000000000^6273 ≤ 43882951928991^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374468337 10000000000 43882951928991 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (644598013/1250000000 : ℝ)^8321 ≤ (5192623761537/12500000000000 : ℝ)^6273 := by
    have hnat : (644598013 : ℕ)^8321*12500000000000^6273 ≤ 5192623761537^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644598013 1250000000 5192623761537 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (292683721/1250000000 : ℝ)^8321 ≤ (2915211593113/20000000000000 : ℝ)^6273 := by
    have hnat : (292683721 : ℕ)^8321*20000000000000^6273 ≤ 2915211593113^6273*1250000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292683721 1250000000 2915211593113 20000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374468337/10000000000 : ℝ), (644598013/1250000000 : ℝ), (-292683721/1250000000 : ℝ)] ![(43882951928991/100000000000000 : ℝ), (5192623761537/12500000000000 : ℝ), (2915211593113/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374468337/10000000000 : ℝ)|^8321 ≤ (43882951928991/100000000000000 : ℝ)^6273
        have hw : |(5374468337/10000000000 : ℝ)|=(5374468337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(644598013/1250000000 : ℝ)|^8321 ≤ (5192623761537/12500000000000 : ℝ)^6273
        have hw : |(644598013/1250000000 : ℝ)|=(644598013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-292683721/1250000000 : ℝ)|^8321 ≤ (2915211593113/20000000000000 : ℝ)^6273
        have hw : |(-292683721/1250000000 : ℝ)|=(292683721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s2_3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355624127/10000000000 : ℝ)*x 0 + (401605713/1000000000 : ℝ)*x 1 + (2361886237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355624127/10000000000 : ℝ)^8321 ≤ (2075334497403/6250000000000 : ℝ)^6273 := by
    have hnat : (4355624127 : ℕ)^8321*6250000000000^6273 ≤ 2075334497403^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355624127 10000000000 2075334497403 6250000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401605713/1000000000 : ℝ)^8321 ≤ (29815976585357/100000000000000 : ℝ)^6273 := by
    have hnat : (401605713 : ℕ)^8321*100000000000000^6273 ≤ 29815976585357^6273*1000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401605713 1000000000 29815976585357 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2361886237/5000000000 : ℝ)^8321 ≤ (1848933571751/5000000000000 : ℝ)^6273 := by
    have hnat : (2361886237 : ℕ)^8321*5000000000000^6273 ≤ 1848933571751^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2361886237 5000000000 1848933571751 5000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355624127/10000000000 : ℝ), (401605713/1000000000 : ℝ), (2361886237/5000000000 : ℝ)] ![(2075334497403/6250000000000 : ℝ), (29815976585357/100000000000000 : ℝ), (1848933571751/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355624127/10000000000 : ℝ)|^8321 ≤ (2075334497403/6250000000000 : ℝ)^6273
        have hw : |(4355624127/10000000000 : ℝ)|=(4355624127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(401605713/1000000000 : ℝ)|^8321 ≤ (29815976585357/100000000000000 : ℝ)^6273
        have hw : |(401605713/1000000000 : ℝ)|=(401605713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2361886237/5000000000 : ℝ)|^8321 ≤ (1848933571751/5000000000000 : ℝ)^6273
        have hw : |(2361886237/5000000000 : ℝ)|=(2361886237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s2_4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1078009857/5000000000 : ℝ)*x 0 + (5159266541/10000000000 : ℝ)*x 1 + (5510984313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078009857/5000000000 : ℝ)^8321 ≤ (13064856091541/100000000000000 : ℝ)^6273 := by
    have hnat : (1078009857 : ℕ)^8321*100000000000000^6273 ≤ 13064856091541^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078009857 5000000000 13064856091541 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5159266541/10000000000 : ℝ)^8321 ≤ (5195939807181/12500000000000 : ℝ)^6273 := by
    have hnat : (5159266541 : ℕ)^8321*12500000000000^6273 ≤ 5195939807181^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5159266541 10000000000 5195939807181 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5510984313/10000000000 : ℝ)^8321 ≤ (4536762544043/10000000000000 : ℝ)^6273 := by
    have hnat : (5510984313 : ℕ)^8321*10000000000000^6273 ≤ 4536762544043^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510984313 10000000000 4536762544043 10000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1078009857/5000000000 : ℝ), (5159266541/10000000000 : ℝ), (5510984313/10000000000 : ℝ)] ![(13064856091541/100000000000000 : ℝ), (5195939807181/12500000000000 : ℝ), (4536762544043/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1078009857/5000000000 : ℝ)|^8321 ≤ (13064856091541/100000000000000 : ℝ)^6273
        have hw : |(-1078009857/5000000000 : ℝ)|=(1078009857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5159266541/10000000000 : ℝ)|^8321 ≤ (5195939807181/12500000000000 : ℝ)^6273
        have hw : |(5159266541/10000000000 : ℝ)|=(5159266541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5510984313/10000000000 : ℝ)|^8321 ≤ (4536762544043/10000000000000 : ℝ)^6273
        have hw : |(5510984313/10000000000 : ℝ)|=(5510984313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s2_5 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5284046211/10000000000 : ℝ)*x 0 + (-1987267729/10000000000 : ℝ)*x 1 + (2755492437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284046211/10000000000 : ℝ)^8321 ≤ (42906307815861/100000000000000 : ℝ)^6273 := by
    have hnat : (5284046211 : ℕ)^8321*100000000000000^6273 ≤ 42906307815861^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284046211 10000000000 42906307815861 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1987267729/10000000000 : ℝ)^8321 ≤ (1465757575449/12500000000000 : ℝ)^6273 := by
    have hnat : (1987267729 : ℕ)^8321*12500000000000^6273 ≤ 1465757575449^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987267729 10000000000 1465757575449 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2755492437/5000000000 : ℝ)^8321 ≤ (5670953945809/12500000000000 : ℝ)^6273 := by
    have hnat : (2755492437 : ℕ)^8321*12500000000000^6273 ≤ 5670953945809^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755492437 5000000000 5670953945809 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284046211/10000000000 : ℝ), (-1987267729/10000000000 : ℝ), (2755492437/5000000000 : ℝ)] ![(42906307815861/100000000000000 : ℝ), (1465757575449/12500000000000 : ℝ), (5670953945809/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284046211/10000000000 : ℝ)|^8321 ≤ (42906307815861/100000000000000 : ℝ)^6273
        have hw : |(5284046211/10000000000 : ℝ)|=(5284046211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1987267729/10000000000 : ℝ)|^8321 ≤ (1465757575449/12500000000000 : ℝ)^6273
        have hw : |(-1987267729/10000000000 : ℝ)|=(1987267729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2755492437/5000000000 : ℝ)|^8321 ≤ (5670953945809/12500000000000 : ℝ)^6273
        have hw : |(2755492437/5000000000 : ℝ)|=(2755492437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s2_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5284044953/10000000000 : ℝ)*x 0 + (5510984741/10000000000 : ℝ)*x 1 + (-993634823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284044953/10000000000 : ℝ)^8321 ≤ (42906294265983/100000000000000 : ℝ)^6273 := by
    have hnat : (5284044953 : ℕ)^8321*100000000000000^6273 ≤ 42906294265983^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284044953 10000000000 42906294265983 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510984741/10000000000 : ℝ)^8321 ≤ (45367630114131/100000000000000 : ℝ)^6273 := by
    have hnat : (5510984741 : ℕ)^8321*100000000000000^6273 ≤ 45367630114131^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510984741 10000000000 45367630114131 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (993634823/5000000000 : ℝ)^8321 ≤ (1465759450997/12500000000000 : ℝ)^6273 := by
    have hnat : (993634823 : ℕ)^8321*12500000000000^6273 ≤ 1465759450997^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993634823 5000000000 1465759450997 12500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284044953/10000000000 : ℝ), (5510984741/10000000000 : ℝ), (-993634823/5000000000 : ℝ)] ![(42906294265983/100000000000000 : ℝ), (45367630114131/100000000000000 : ℝ), (1465759450997/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284044953/10000000000 : ℝ)|^8321 ≤ (42906294265983/100000000000000 : ℝ)^6273
        have hw : |(5284044953/10000000000 : ℝ)|=(5284044953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510984741/10000000000 : ℝ)|^8321 ≤ (45367630114131/100000000000000 : ℝ)^6273
        have hw : |(5510984741/10000000000 : ℝ)|=(5510984741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-993634823/5000000000 : ℝ)|^8321 ≤ (1465759450997/12500000000000 : ℝ)^6273
        have hw : |(-993634823/5000000000 : ℝ)|=(993634823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1128_s2_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177917533/5000000000 : ℝ)*x 0 + (4718845279/10000000000 : ℝ)*x 1 + (2010516981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177917533/5000000000 : ℝ)^8321 ≤ (33207485092967/100000000000000 : ℝ)^6273 := by
    have hnat : (2177917533 : ℕ)^8321*100000000000000^6273 ≤ 33207485092967^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177917533 5000000000 33207485092967 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4718845279/10000000000 : ℝ)^8321 ≤ (36927516404627/100000000000000 : ℝ)^6273 := by
    have hnat : (4718845279 : ℕ)^8321*100000000000000^6273 ≤ 36927516404627^6273*10000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4718845279 10000000000 36927516404627 100000000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2010516981/5000000000 : ℝ)^8321 ≤ (746624962283/2500000000000 : ℝ)^6273 := by
    have hnat : (2010516981 : ℕ)^8321*2500000000000^6273 ≤ 746624962283^6273*5000000000^8321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010516981 5000000000 746624962283 2500000000000 8321 6273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8321/2048 : ℝ)) 8321 6273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177917533/5000000000 : ℝ), (4718845279/10000000000 : ℝ), (2010516981/5000000000 : ℝ)] ![(33207485092967/100000000000000 : ℝ), (36927516404627/100000000000000 : ℝ), (746624962283/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177917533/5000000000 : ℝ)|^8321 ≤ (33207485092967/100000000000000 : ℝ)^6273
        have hw : |(2177917533/5000000000 : ℝ)|=(2177917533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4718845279/10000000000 : ℝ)|^8321 ≤ (36927516404627/100000000000000 : ℝ)^6273
        have hw : |(4718845279/10000000000 : ℝ)|=(4718845279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2010516981/5000000000 : ℝ)|^8321 ≤ (746624962283/2500000000000 : ℝ)^6273
        have hw : |(2010516981/5000000000 : ℝ)|=(2010516981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1128_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20501/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5571/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4503/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3309/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20501/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5571/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20501/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5571/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20501/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5571/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20501/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5571/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20501/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5571/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20501/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5571/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5571/100000 : ℝ) ^ (65/16 : ℝ) ≤ (402090174306823/50000000000000000000 : ℝ) := by
    have hpowers : (5571/100000 : ℝ)^65 ≤ (402090174306823/50000000000000000000 : ℝ)^16 := by
      have hnat : (5571 : ℕ)^65*50000000000000000000^16 ≤ 402090174306823^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5571 100000 402090174306823 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5571/100000 : ℝ)) (X := (402090174306823/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hpowhi : (20501/100000 : ℝ) ^ (65/16 : ℝ) ≤ (15998752608942001/10000000000000000000 : ℝ) := by
    have hpowers : (20501/100000 : ℝ)^65 ≤ (15998752608942001/10000000000000000000 : ℝ)^16 := by
      have hnat : (20501 : ℕ)^65*10000000000000000000^16 ≤ 15998752608942001^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20501 100000 15998752608942001 10000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20501/100000 : ℝ)) (X := (15998752608942001/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000402090174306823/25000000000000000000 : ℝ) ≤ (10000039590177157/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (25000402090174306823/25000000000000000000 : ℝ)^16 ≤ (10000039590177157/10000000000000000 : ℝ)^65 := by
      have hnat : (25000402090174306823 : ℕ)^16*10000000000000000^65 ≤ 10000039590177157^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000402090174306823 25000000000000000000 10000039590177157 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000039590177157/10000000000000000 : ℝ)) (X := (25000402090174306823/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (12520098963304754207/12500000000000000000 : ℝ) ≤ (1000395555319017/1000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (12520098963304754207/12500000000000000000 : ℝ)^16 ≤ (1000395555319017/1000000000000000 : ℝ)^65 := by
      have hnat : (12520098963304754207 : ℕ)^16*1000000000000000^65 ≤ 1000395555319017^65*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12520098963304754207 12500000000000000000 1000395555319017 1000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000395555319017/1000000000000000 : ℝ)) (X := (12520098963304754207/12500000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (5015998752608942001/5000000000000000000 : ℝ) ≤ (10007871516203183/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (5015998752608942001/5000000000000000000 : ℝ)^16 ≤ (10007871516203183/10000000000000000 : ℝ)^65 := by
      have hnat : (5015998752608942001 : ℕ)^16*10000000000000000^65 ≤ 10007871516203183^65*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5015998752608942001 5000000000000000000 10007871516203183 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007871516203183/10000000000000000 : ℝ)) (X := (5015998752608942001/5000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(402090174306823/50000000000000000000 : ℝ) ≤ ((37314239855363490791/37325000000000000000 : ℝ)+2*(3915963013013/1493000000000000 : ℝ)*(5571/100000 : ℝ))^(65/16 : ℝ) := by
    rw [show (37314239855363490791/37325000000000000000 : ℝ)+2*(3915963013013/1493000000000000 : ℝ)*(5571/100000 : ℝ)=(10000039590177157/10000000000000000 : ℝ) by norm_num, show 1+2*(402090174306823/50000000000000000000 : ℝ)=(25000402090174306823/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15998752608942001/10000000000000000000 : ℝ)+(402090174306823/50000000000000000000 : ℝ) ≤ ((37314239855363490791/37325000000000000000 : ℝ)+(3915963013013/1493000000000000 : ℝ)*((20501/100000 : ℝ)+(5571/100000 : ℝ)))^(65/16 : ℝ) := by
    rw [show (37314239855363490791/37325000000000000000 : ℝ)+(3915963013013/1493000000000000 : ℝ)*((20501/100000 : ℝ)+(5571/100000 : ℝ))=(1000395555319017/1000000000000000 : ℝ) by norm_num, show 1+(15998752608942001/10000000000000000000 : ℝ)+(402090174306823/50000000000000000000 : ℝ)=(12520098963304754207/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15998752608942001/10000000000000000000 : ℝ) ≤ ((37314239855363490791/37325000000000000000 : ℝ)+2*(3915963013013/1493000000000000 : ℝ)*(20501/100000 : ℝ))^(65/16 : ℝ) := by
    rw [show (37314239855363490791/37325000000000000000 : ℝ)+2*(3915963013013/1493000000000000 : ℝ)*(20501/100000 : ℝ)=(10007871516203183/10000000000000000 : ℝ) by norm_num, show 1+2*(15998752608942001/10000000000000000000 : ℝ)=(5015998752608942001/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37314239855363490791/37325000000000000000 : ℝ)*(X 1 0+X 2 0)+(3915963013013/1493000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (5571/100000 : ℝ)) (hi := (20501/100000 : ℝ)) (c := (37314239855363490791/37325000000000000000 : ℝ)) (alpha := (3915963013013/1493000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37314239855363490791/37325000000000000000 : ℝ)*(X 0 1+X 2 1)+(3915963013013/1493000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (5571/100000 : ℝ)) (hi := (20501/100000 : ℝ)) (c := (37314239855363490791/37325000000000000000 : ℝ)) (alpha := (3915963013013/1493000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37314239855363490791/37325000000000000000 : ℝ)*(X 0 2+X 1 2)+(3915963013013/1493000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (65/16 : ℝ)) (lo := (5571/100000 : ℝ)) (hi := (20501/100000 : ℝ)) (c := (37314239855363490791/37325000000000000000 : ℝ)) (alpha := (3915963013013/1493000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2155913139/10000000000 : ℝ)*X 0 0+(2756746797/5000000000 : ℝ)*X 0 1+(2578391209/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5374468413/10000000000 : ℝ)*X 1 0+(-1170734849/5000000000 : ℝ)*X 1 1+(5156784081/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5374468337/10000000000 : ℝ)*X 2 0+(644598013/1250000000 : ℝ)*X 2 1+(-292683721/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355624127/10000000000 : ℝ)*X 0 0+(401605713/1000000000 : ℝ)*X 0 1+(2361886237/5000000000 : ℝ)*X 0 2+(4355624127/10000000000 : ℝ)*X 1 0+(401605713/1000000000 : ℝ)*X 1 1+(2361886237/5000000000 : ℝ)*X 1 2+(4355624127/10000000000 : ℝ)*X 2 0+(401605713/1000000000 : ℝ)*X 2 1+(2361886237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1078009857/5000000000 : ℝ)*X 0 0+(5159266541/10000000000 : ℝ)*X 0 1+(5510984313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5284046211/10000000000 : ℝ)*X 1 0+(-1987267729/10000000000 : ℝ)*X 1 1+(2755492437/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5284044953/10000000000 : ℝ)*X 2 0+(5510984741/10000000000 : ℝ)*X 2 1+(-993634823/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177917533/5000000000 : ℝ)*X 0 0+(4718845279/10000000000 : ℝ)*X 0 1+(2010516981/5000000000 : ℝ)*X 0 2+(2177917533/5000000000 : ℝ)*X 1 0+(4718845279/10000000000 : ℝ)*X 1 1+(2010516981/5000000000 : ℝ)*X 1 2+(2177917533/5000000000 : ℝ)*X 2 0+(4718845279/10000000000 : ℝ)*X 2 1+(2010516981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1128_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4144303055830511105530691061/373250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (173442001/12500000000000 : ℝ)*(base19) + (135223751/12500000000000 : ℝ)*(base23) + (32080757/10000000000000 : ℝ)*(upper3) + (28603221/20000000000000 : ℝ)*(upper4) + (8099709/12500000000000 : ℝ)*(upper5) + (421645212395343/20000000000000 : ℝ)*(major0) + (421645212395343/20000000000000 : ℝ)*(major1) + (421645212395343/20000000000000 : ℝ)*(major2) + (560682887397703/20000000000000 : ℝ)*(sp0) + (280343612718719/10000000000000 : ℝ)*(sp1) + (2803436432933191/100000000000000 : ℝ)*(sp2) + (1413004629712271/100000000000000 : ℝ)*(sp3) + (23077734683/100000000000000 : ℝ)*(sp4) + (240235207/2500000000000 : ℝ)*(sp7) + (176626779890069/12500000000000 : ℝ)*(f.failure) + (1401718757361599/50000000000000 : ℝ)*(f.sum) + (74212276723959/14930000000000000000000000000 : ℝ)*base65 + (569418562613761313/746500000000000000000000000000000 : ℝ)*base67 + (4681645121963761313/746500000000000000000000000000000 : ℝ)*base69 + (6108619060227761313/746500000000000000000000000000000 : ℝ)*base71 + (38072508509559/14930000000000000000000000000 : ℝ)*base73 + (4343663305092738687/746500000000000000000000000000000 : ℝ)*base76 + (1724690391117261313/746500000000000000000000000000000 : ℝ)*base77 + (10823351990557738687/746500000000000000000000000000000 : ℝ)*base80 + (66397997197279/14930000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (543941/78125000000000000000 : ℝ)*base89 + (543941/78125000000000000000 : ℝ)*base91 + (543941/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10155505134894968697813184629/933125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1004748653/50000000000000 : ℝ)*(base19) + (371219183/25000000000000 : ℝ)*(base23) + (27547793/12500000000000 : ℝ)*(upper2) + (70489451/50000000000000 : ℝ)*(upper3) + (605033/200000000000 : ℝ)*(upper5) + (2138117115325627/100000000000000 : ℝ)*(major0) + (2138117115325627/100000000000000 : ℝ)*(major1) + (2138117115325627/100000000000000 : ℝ)*(major2) + (3248828783/12500000000000 : ℝ)*(sp1) + (5258112813/50000000000000 : ℝ)*(sp2) + (355398186809963/12500000000000 : ℝ)*(sp4) + (1421578747176067/50000000000000 : ℝ)*(sp5) + (568634698675469/20000000000000 : ℝ)*(sp6) + (44782761668561/3125000000000 : ℝ)*(sp7) + (44782761668561/3125000000000 : ℝ)*(f.failure) + (355398186809963/12500000000000 : ℝ)*(f.sum) + (111327217154249/74650000000000000000000000000 : ℝ)*base66 + (31647390388244575957/3732500000000000000000000000000000 : ℝ)*base67 + (13738856719435424043/3732500000000000000000000000000000 : ℝ)*base70 + (6573576384899575957/3732500000000000000000000000000000 : ℝ)*base71 + (537598329661651/74650000000000000000000000000 : ℝ)*base73 + (6361532365654575957/3732500000000000000000000000000000 : ℝ)*base75 + (24995410603867075957/3732500000000000000000000000000000 : ℝ)*base77 + (38987135582482075957/3732500000000000000000000000000000 : ℝ)*base79 + (421267821950749/74650000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (249117/39062500000000000000 : ℝ)*base90 + (249117/39062500000000000000 : ℝ)*base92 + (249117/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1128_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20501/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5571/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4503/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3309/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1128_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1128_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4503/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3309/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1128_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1128_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1128_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (8321/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9325039/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4503/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3309/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1128_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

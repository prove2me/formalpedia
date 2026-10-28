-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1119_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:08:53.023333+00:00
-- url     : https://prove2.me/submissions/e440d35c-85b8-4853-9c34-713a6bfbf40b

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
theorem support_rectangle_w1119_s6_0 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2177896881/10000000000 : ℝ)*x 0 + (5393847049/10000000000 : ℝ)*x 1 + (526498473/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177896881/10000000000 : ℝ)^1039 ≤ (1323153337021/10000000000000 : ℝ)^783 := by
    have hnat : (2177896881 : ℕ)^1039*10000000000000^783 ≤ 1323153337021^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177896881 10000000000 1323153337021 10000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393847049/10000000000 : ℝ)^1039 ≤ (8816039197597/20000000000000 : ℝ)^783 := by
    have hnat : (5393847049 : ℕ)^1039*20000000000000^783 ≤ 8816039197597^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393847049 10000000000 8816039197597 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526498473/1000000000 : ℝ)^1039 ≤ (8537654127157/20000000000000 : ℝ)^783 := by
    have hnat : (526498473 : ℕ)^1039*20000000000000^783 ≤ 8537654127157^783*1000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526498473 1000000000 8537654127157 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2177896881/10000000000 : ℝ), (5393847049/10000000000 : ℝ), (526498473/1000000000 : ℝ)] ![(1323153337021/10000000000000 : ℝ), (8816039197597/20000000000000 : ℝ), (8537654127157/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2177896881/10000000000 : ℝ)|^1039 ≤ (1323153337021/10000000000000 : ℝ)^783
        have hw : |(-2177896881/10000000000 : ℝ)|=(2177896881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393847049/10000000000 : ℝ)|^1039 ≤ (8816039197597/20000000000000 : ℝ)^783
        have hw : |(5393847049/10000000000 : ℝ)|=(5393847049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526498473/1000000000 : ℝ)|^1039 ≤ (8537654127157/20000000000000 : ℝ)^783
        have hw : |(526498473/1000000000 : ℝ)|=(526498473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s6_1 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336234701/2500000000 : ℝ)*x 0 + (-2190693/9765625 : ℝ)*x 1 + (2632492369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336234701/2500000000 : ℝ)^1039 ≤ (871012231067/2000000000000 : ℝ)^783 := by
    have hnat : (1336234701 : ℕ)^1039*2000000000000^783 ≤ 871012231067^783*2500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336234701 2500000000 871012231067 2000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190693/9765625 : ℝ)^1039 ≤ (6880558856129/50000000000000 : ℝ)^783 := by
    have hnat : (2190693 : ℕ)^1039*50000000000000^783 ≤ 6880558856129^783*9765625^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190693 9765625 6880558856129 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632492369/5000000000 : ℝ)^1039 ≤ (667004230029/1562500000000 : ℝ)^783 := by
    have hnat : (2632492369 : ℕ)^1039*1562500000000^783 ≤ 667004230029^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632492369 5000000000 667004230029 1562500000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336234701/2500000000 : ℝ), (-2190693/9765625 : ℝ), (2632492369/5000000000 : ℝ)] ![(871012231067/2000000000000 : ℝ), (6880558856129/50000000000000 : ℝ), (667004230029/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336234701/2500000000 : ℝ)|^1039 ≤ (871012231067/2000000000000 : ℝ)^783
        have hw : |(1336234701/2500000000 : ℝ)|=(1336234701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2190693/9765625 : ℝ)|^1039 ≤ (6880558856129/50000000000000 : ℝ)^783
        have hw : |(-2190693/9765625 : ℝ)|=(2190693/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632492369/5000000000 : ℝ)|^1039 ≤ (667004230029/1562500000000 : ℝ)^783
        have hw : |(2632492369/5000000000 : ℝ)|=(2632492369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s6_2 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (167029337/312500000 : ℝ)*x 0 + (2632492379/5000000000 : ℝ)*x 1 + (-2243269631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167029337/312500000 : ℝ)^1039 ≤ (4355061133711/10000000000000 : ℝ)^783 := by
    have hnat : (167029337 : ℕ)^1039*10000000000000^783 ≤ 4355061133711^783*312500000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167029337 312500000 4355061133711 10000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632492379/5000000000 : ℝ)^1039 ≤ (42688270937033/100000000000000 : ℝ)^783 := by
    have hnat : (2632492379 : ℕ)^1039*100000000000000^783 ≤ 42688270937033^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632492379 5000000000 42688270937033 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243269631/10000000000 : ℝ)^1039 ≤ (6880558852059/50000000000000 : ℝ)^783 := by
    have hnat : (2243269631 : ℕ)^1039*50000000000000^783 ≤ 6880558852059^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243269631 10000000000 6880558852059 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167029337/312500000 : ℝ), (2632492379/5000000000 : ℝ), (-2243269631/10000000000 : ℝ)] ![(4355061133711/10000000000000 : ℝ), (42688270937033/100000000000000 : ℝ), (6880558852059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167029337/312500000 : ℝ)|^1039 ≤ (4355061133711/10000000000000 : ℝ)^783
        have hw : |(167029337/312500000 : ℝ)|=(167029337/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632492379/5000000000 : ℝ)|^1039 ≤ (42688270937033/100000000000000 : ℝ)^783
        have hw : |(2632492379/5000000000 : ℝ)|=(2632492379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2243269631/10000000000 : ℝ)|^1039 ≤ (6880558852059/50000000000000 : ℝ)^783
        have hw : |(-2243269631/10000000000 : ℝ)|=(2243269631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s6_3 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4367903627/10000000000 : ℝ)*x 0 + (848432477/2000000000 : ℝ)*x 1 + (4497374519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367903627/10000000000 : ℝ)^1039 ≤ (16658319013427/50000000000000 : ℝ)^783 := by
    have hnat : (4367903627 : ℕ)^1039*50000000000000^783 ≤ 16658319013427^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367903627 10000000000 16658319013427 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848432477/2000000000 : ℝ)^1039 ≤ (32049985159023/100000000000000 : ℝ)^783 := by
    have hnat : (848432477 : ℕ)^1039*100000000000000^783 ≤ 32049985159023^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848432477 2000000000 32049985159023 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497374519/10000000000 : ℝ)^1039 ≤ (4329172100357/12500000000000 : ℝ)^783 := by
    have hnat : (4497374519 : ℕ)^1039*12500000000000^783 ≤ 4329172100357^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497374519 10000000000 4329172100357 12500000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367903627/10000000000 : ℝ), (848432477/2000000000 : ℝ), (4497374519/10000000000 : ℝ)] ![(16658319013427/50000000000000 : ℝ), (32049985159023/100000000000000 : ℝ), (4329172100357/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367903627/10000000000 : ℝ)|^1039 ≤ (16658319013427/50000000000000 : ℝ)^783
        have hw : |(4367903627/10000000000 : ℝ)|=(4367903627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(848432477/2000000000 : ℝ)|^1039 ≤ (32049985159023/100000000000000 : ℝ)^783
        have hw : |(848432477/2000000000 : ℝ)|=(848432477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497374519/10000000000 : ℝ)|^1039 ≤ (4329172100357/12500000000000 : ℝ)^783
        have hw : |(4497374519/10000000000 : ℝ)|=(4497374519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s6_4 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2177901917/10000000000 : ℝ)*x 0 + (526531019/1000000000 : ℝ)*x 1 + (5393520401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177901917/10000000000 : ℝ)^1039 ≤ (3307893492237/25000000000000 : ℝ)^783 := by
    have hnat : (2177901917 : ℕ)^1039*25000000000000^783 ≤ 3307893492237^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177901917 10000000000 3307893492237 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526531019/1000000000 : ℝ)^1039 ≤ (42691772241477/100000000000000 : ℝ)^783 := by
    have hnat : (526531019 : ℕ)^1039*100000000000000^783 ≤ 42691772241477^783*1000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526531019 1000000000 42691772241477 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393520401/10000000000 : ℝ)^1039 ≤ (2203832688869/5000000000000 : ℝ)^783 := by
    have hnat : (5393520401 : ℕ)^1039*5000000000000^783 ≤ 2203832688869^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393520401 10000000000 2203832688869 5000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2177901917/10000000000 : ℝ), (526531019/1000000000 : ℝ), (5393520401/10000000000 : ℝ)] ![(3307893492237/25000000000000 : ℝ), (42691772241477/100000000000000 : ℝ), (2203832688869/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2177901917/10000000000 : ℝ)|^1039 ≤ (3307893492237/25000000000000 : ℝ)^783
        have hw : |(-2177901917/10000000000 : ℝ)|=(2177901917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526531019/1000000000 : ℝ)|^1039 ≤ (42691772241477/100000000000000 : ℝ)^783
        have hw : |(526531019/1000000000 : ℝ)|=(526531019/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393520401/10000000000 : ℝ)|^1039 ≤ (2203832688869/5000000000000 : ℝ)^783
        have hw : |(5393520401/10000000000 : ℝ)|=(5393520401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s6_5 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312347173/10000000000 : ℝ)*x 0 + (-105736699/500000000 : ℝ)*x 1 + (2696760201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312347173/10000000000 : ℝ)^1039 ≤ (8639716633813/20000000000000 : ℝ)^783 := by
    have hnat : (5312347173 : ℕ)^1039*20000000000000^783 ≤ 8639716633813^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312347173 10000000000 8639716633813 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105736699/500000000 : ℝ)^1039 ≤ (6362381514577/50000000000000 : ℝ)^783 := by
    have hnat : (105736699 : ℕ)^1039*50000000000000^783 ≤ 6362381514577^783*500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105736699 500000000 6362381514577 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696760201/5000000000 : ℝ)^1039 ≤ (688697715441/1562500000000 : ℝ)^783 := by
    have hnat : (2696760201 : ℕ)^1039*1562500000000^783 ≤ 688697715441^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696760201 5000000000 688697715441 1562500000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312347173/10000000000 : ℝ), (-105736699/500000000 : ℝ), (2696760201/5000000000 : ℝ)] ![(8639716633813/20000000000000 : ℝ), (6362381514577/50000000000000 : ℝ), (688697715441/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312347173/10000000000 : ℝ)|^1039 ≤ (8639716633813/20000000000000 : ℝ)^783
        have hw : |(5312347173/10000000000 : ℝ)|=(5312347173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105736699/500000000 : ℝ)|^1039 ≤ (6362381514577/50000000000000 : ℝ)^783
        have hw : |(-105736699/500000000 : ℝ)|=(105736699/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696760201/5000000000 : ℝ)|^1039 ≤ (688697715441/1562500000000 : ℝ)^783
        have hw : |(2696760201/5000000000 : ℝ)|=(2696760201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s6_6 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328086793/2500000000 : ℝ)*x 0 + (1078704081/2000000000 : ℝ)*x 1 + (-2114733977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328086793/2500000000 : ℝ)^1039 ≤ (1727943326331/4000000000000 : ℝ)^783 := by
    have hnat : (1328086793 : ℕ)^1039*4000000000000^783 ≤ 1727943326331^783*2500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328086793 2500000000 1727943326331 4000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078704081/2000000000 : ℝ)^1039 ≤ (11019163455189/25000000000000 : ℝ)^783 := by
    have hnat : (1078704081 : ℕ)^1039*25000000000000^783 ≤ 11019163455189^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078704081 2000000000 11019163455189 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114733977/10000000000 : ℝ)^1039 ≤ (31811907513/250000000000 : ℝ)^783 := by
    have hnat : (2114733977 : ℕ)^1039*250000000000^783 ≤ 31811907513^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114733977 10000000000 31811907513 250000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328086793/2500000000 : ℝ), (1078704081/2000000000 : ℝ), (-2114733977/10000000000 : ℝ)] ![(1727943326331/4000000000000 : ℝ), (11019163455189/25000000000000 : ℝ), (31811907513/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328086793/2500000000 : ℝ)|^1039 ≤ (1727943326331/4000000000000 : ℝ)^783
        have hw : |(1328086793/2500000000 : ℝ)|=(1328086793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078704081/2000000000 : ℝ)|^1039 ≤ (11019163455189/25000000000000 : ℝ)^783
        have hw : |(1078704081/2000000000 : ℝ)|=(1078704081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2114733977/10000000000 : ℝ)|^1039 ≤ (31811907513/250000000000 : ℝ)^783
        have hw : |(-2114733977/10000000000 : ℝ)|=(2114733977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s6_7 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (436791357/1000000000 : ℝ)*x 0 + (4496729987/10000000000 : ℝ)*x 1 + (1060702319/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436791357/1000000000 : ℝ)^1039 ≤ (16658369332139/50000000000000 : ℝ)^783 := by
    have hnat : (436791357 : ℕ)^1039*50000000000000^783 ≤ 16658369332139^783*1000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436791357 1000000000 16658369332139 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496729987/10000000000 : ℝ)^1039 ≤ (4328348846279/12500000000000 : ℝ)^783 := by
    have hnat : (4496729987 : ℕ)^1039*12500000000000^783 ≤ 4328348846279^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496729987 10000000000 4328348846279 12500000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060702319/2500000000 : ℝ)^1039 ≤ (3205647055151/10000000000000 : ℝ)^783 := by
    have hnat : (1060702319 : ℕ)^1039*10000000000000^783 ≤ 3205647055151^783*2500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060702319 2500000000 3205647055151 10000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436791357/1000000000 : ℝ), (4496729987/10000000000 : ℝ), (1060702319/2500000000 : ℝ)] ![(16658369332139/50000000000000 : ℝ), (4328348846279/12500000000000 : ℝ), (3205647055151/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436791357/1000000000 : ℝ)|^1039 ≤ (16658369332139/50000000000000 : ℝ)^783
        have hw : |(436791357/1000000000 : ℝ)|=(436791357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496729987/10000000000 : ℝ)|^1039 ≤ (4328348846279/12500000000000 : ℝ)^783
        have hw : |(4496729987/10000000000 : ℝ)|=(4496729987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060702319/2500000000 : ℝ)|^1039 ≤ (3205647055151/10000000000000 : ℝ)^783
        have hw : |(1060702319/2500000000 : ℝ)|=(1060702319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1119_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2263/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3511/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11281/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11281/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11281/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11281/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11281/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11281/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11281/100000 : ℝ) ^ (8311/2048 : ℝ) ≤ (14266801210149667/100000000000000000000 : ℝ) := by
    have hpowers : (11281/100000 : ℝ)^8311 ≤ (14266801210149667/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11281 : ℕ)^8311*100000000000000000000^2048 ≤ 14266801210149667^2048*100000^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11281 100000 14266801210149667 100000000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11281/100000 : ℝ)) (X := (14266801210149667/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (88/625 : ℝ) ^ (8311/2048 : ℝ) ≤ (4383790492176601/12500000000000000000 : ℝ) := by
    have hpowers : (88/625 : ℝ)^8311 ≤ (4383790492176601/12500000000000000000 : ℝ)^2048 := by
      have hnat : (88 : ℕ)^8311*12500000000000000000^2048 ≤ 4383790492176601^2048*625^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88 625 4383790492176601 12500000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88/625 : ℝ)) (X := (4383790492176601/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014266801210149667/50000000000000000000 : ℝ) ≤ (5000351525304793/5000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (50014266801210149667/50000000000000000000 : ℝ)^2048 ≤ (5000351525304793/5000000000000000 : ℝ)^8311 := by
      have hnat : (50014266801210149667 : ℕ)^2048*5000000000000000^8311 ≤ 5000351525304793^8311*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014266801210149667 50000000000000000000 5000351525304793 5000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000351525304793/5000000000000000 : ℝ)) (X := (50014266801210149667/50000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001973485005902499/4000000000000000000 : ℝ) ≤ (2000243108300341/2000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (4001973485005902499/4000000000000000000 : ℝ)^2048 ≤ (2000243108300341/2000000000000000 : ℝ)^8311 := by
      have hnat : (4001973485005902499 : ℕ)^2048*2000000000000000^8311 ≤ 2000243108300341^8311*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001973485005902499 4000000000000000000 2000243108300341 2000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000243108300341/2000000000000000 : ℝ)) (X := (4001973485005902499/4000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254383790492176601/6250000000000000000 : ℝ) ≤ (312554001012307/312500000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (6254383790492176601/6250000000000000000 : ℝ)^2048 ≤ (312554001012307/312500000000000 : ℝ)^8311 := by
      have hnat : (6254383790492176601 : ℕ)^2048*312500000000000^8311 ≤ 312554001012307^8311*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254383790492176601 6250000000000000000 312554001012307 312500000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312554001012307/312500000000000 : ℝ)) (X := (6254383790492176601/6250000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14266801210149667/100000000000000000000 : ℝ) ≤ ((291462552282794191/291562500000000000 : ℝ)+2*(170830297373/93300000000000 : ℝ)*(11281/100000 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (291462552282794191/291562500000000000 : ℝ)+2*(170830297373/93300000000000 : ℝ)*(11281/100000 : ℝ)=(5000351525304793/5000000000000000 : ℝ) by norm_num, show 1+2*(14266801210149667/100000000000000000000 : ℝ)=(50014266801210149667/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4383790492176601/12500000000000000000 : ℝ)+(14266801210149667/100000000000000000000 : ℝ) ≤ ((291462552282794191/291562500000000000 : ℝ)+(170830297373/93300000000000 : ℝ)*((88/625 : ℝ)+(11281/100000 : ℝ)))^(8311/2048 : ℝ) := by
    rw [show (291462552282794191/291562500000000000 : ℝ)+(170830297373/93300000000000 : ℝ)*((88/625 : ℝ)+(11281/100000 : ℝ))=(2000243108300341/2000000000000000 : ℝ) by norm_num, show 1+(4383790492176601/12500000000000000000 : ℝ)+(14266801210149667/100000000000000000000 : ℝ)=(4001973485005902499/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4383790492176601/12500000000000000000 : ℝ) ≤ ((291462552282794191/291562500000000000 : ℝ)+2*(170830297373/93300000000000 : ℝ)*(88/625 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (291462552282794191/291562500000000000 : ℝ)+2*(170830297373/93300000000000 : ℝ)*(88/625 : ℝ)=(312554001012307/312500000000000 : ℝ) by norm_num, show 1+2*(4383790492176601/12500000000000000000 : ℝ)=(6254383790492176601/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (291462552282794191/291562500000000000 : ℝ)*(X 1 0+X 2 0)+(170830297373/93300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (88/625 : ℝ)) (c := (291462552282794191/291562500000000000 : ℝ)) (alpha := (170830297373/93300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (291462552282794191/291562500000000000 : ℝ)*(X 0 1+X 2 1)+(170830297373/93300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (88/625 : ℝ)) (c := (291462552282794191/291562500000000000 : ℝ)) (alpha := (170830297373/93300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (291462552282794191/291562500000000000 : ℝ)*(X 0 2+X 1 2)+(170830297373/93300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (88/625 : ℝ)) (c := (291462552282794191/291562500000000000 : ℝ)) (alpha := (170830297373/93300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2177896881/10000000000 : ℝ)*X 0 0+(5393847049/10000000000 : ℝ)*X 0 1+(526498473/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336234701/2500000000 : ℝ)*X 1 0+(-2190693/9765625 : ℝ)*X 1 1+(2632492369/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167029337/312500000 : ℝ)*X 2 0+(2632492379/5000000000 : ℝ)*X 2 1+(-2243269631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4367903627/10000000000 : ℝ)*X 0 0+(848432477/2000000000 : ℝ)*X 0 1+(4497374519/10000000000 : ℝ)*X 0 2+(4367903627/10000000000 : ℝ)*X 1 0+(848432477/2000000000 : ℝ)*X 1 1+(4497374519/10000000000 : ℝ)*X 1 2+(4367903627/10000000000 : ℝ)*X 2 0+(848432477/2000000000 : ℝ)*X 2 1+(4497374519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2177901917/10000000000 : ℝ)*X 0 0+(526531019/1000000000 : ℝ)*X 0 1+(5393520401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312347173/10000000000 : ℝ)*X 1 0+(-105736699/500000000 : ℝ)*X 1 1+(2696760201/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328086793/2500000000 : ℝ)*X 2 0+(1078704081/2000000000 : ℝ)*X 2 1+(-2114733977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436791357/1000000000 : ℝ)*X 0 0+(4496729987/10000000000 : ℝ)*X 0 1+(1060702319/2500000000 : ℝ)*X 0 2+(436791357/1000000000 : ℝ)*X 1 0+(4496729987/10000000000 : ℝ)*X 1 1+(1060702319/2500000000 : ℝ)*X 1 2+(436791357/1000000000 : ℝ)*X 2 0+(4496729987/10000000000 : ℝ)*X 2 1+(1060702319/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1865291099030225122595257/485937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (396537947/50000000000000 : ℝ)*(base19) + (3419651/500000000000 : ℝ)*(base23) + (5352147/12500000000000 : ℝ)*(lower2) + (109364391/100000000000000 : ℝ)*(upper3) + (45306879/100000000000000 : ℝ)*(upper5) + (291964885230001/5000000000000 : ℝ)*(major0) + (291964885230001/5000000000000 : ℝ)*(major1) + (291964885230001/5000000000000 : ℝ)*(major2) + (4850152295791/62500000000 : ℝ)*(sp0) + (194006601753539/2500000000000 : ℝ)*(sp1) + (7760264179287253/100000000000000 : ℝ)*(sp2) + (7652966574759/195312500000 : ℝ)*(sp3) + (21189951853/100000000000000 : ℝ)*(sp4) + (11531754597/100000000000000 : ℝ)*(sp7) + (979582604507801/25000000000000 : ℝ)*(f.failure) + (3880132431608727/50000000000000 : ℝ)*(f.sum) + (8678194294273/933000000000000000000000000 : ℝ)*base66 + (46745549659648493/2915625000000000000000000000000 : ℝ)*base68 + (4115169033410993/2915625000000000000000000000000 : ℝ)*base70 + (12690866514013309/1457812500000000000000000000000 : ℝ)*base72 + (238348991791/37320000000000000000000000 : ℝ)*base74 + (1666724755873033/728906250000000000000000000000 : ℝ)*base75 + (21757623642913309/1457812500000000000000000000000 : ℝ)*base78 + (4612621113376507/2915625000000000000000000000000 : ℝ)*base79 + (1949619392881/933000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2794887/625000000000000000000 : ℝ)*base89 + (2794887/625000000000000000000 : ℝ)*base91 + (2794887/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9926635571946910863674867/2429687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (148392327/20000000000000 : ℝ)*(base19) + (813793233/100000000000000 : ℝ)*(base23) + (41175551/50000000000000 : ℝ)*(upper3) + (4068853/12500000000000 : ℝ)*(lower4) + (81066307/100000000000000 : ℝ)*(upper5) + (2934481750319519/50000000000000 : ℝ)*(major0) + (2934481750319519/50000000000000 : ℝ)*(major1) + (2934481750319519/50000000000000 : ℝ)*(major2) + (10122170487/50000000000000 : ℝ)*(sp1) + (2775568173/12500000000000 : ℝ)*(sp2) + (974961234579443/12500000000000 : ℝ)*(sp4) + (974958611291617/12500000000000 : ℝ)*(sp5) + (243739589321779/3125000000000 : ℝ)*(sp6) + (246139811778573/6250000000000 : ℝ)*(sp7) + (246139811778573/6250000000000 : ℝ)*(f.failure) + (974961234579443/12500000000000 : ℝ)*(f.sum) + (4864635611153/2332500000000000000000000000 : ℝ)*base66 + (3345953314457719/911132812500000000000000000000 : ℝ)*base67 + (24752138264681063/1822265625000000000000000000000 : ℝ)*base69 + (4197840072988969/911132812500000000000000000000 : ℝ)*base71 + (1135025423227/2332500000000000000000000000 : ℝ)*base73 + (49282390396471501/3644531250000000000000000000000 : ℝ)*base75 + (3014537631988969/911132812500000000000000000000 : ℝ)*base77 + (12194947097667281/911132812500000000000000000000 : ℝ)*base80 + (3179451316927/2332500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (736549/156250000000000000000 : ℝ)*base90 + (736549/156250000000000000000 : ℝ)*base92 + (736549/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1119_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1119_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1119_s7_0 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-217792979/1000000000 : ℝ)*x 0 + (5393482451/10000000000 : ℝ)*x 1 + (2632663777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217792979/1000000000 : ℝ)^1039 ≤ (13231798673361/100000000000000 : ℝ)^783 := by
    have hnat : (217792979 : ℕ)^1039*100000000000000^783 ≤ 13231798673361^783*1000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217792979 1000000000 13231798673361 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393482451/10000000000 : ℝ)^1039 ≤ (11019060561879/25000000000000 : ℝ)^783 := by
    have hnat : (5393482451 : ℕ)^1039*25000000000000^783 ≤ 11019060561879^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393482451 10000000000 11019060561879 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632663777/5000000000 : ℝ)^1039 ≤ (42691959061757/100000000000000 : ℝ)^783 := by
    have hnat : (2632663777 : ℕ)^1039*100000000000000^783 ≤ 42691959061757^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632663777 5000000000 42691959061757 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217792979/1000000000 : ℝ), (5393482451/10000000000 : ℝ), (2632663777/5000000000 : ℝ)] ![(13231798673361/100000000000000 : ℝ), (11019060561879/25000000000000 : ℝ), (42691959061757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217792979/1000000000 : ℝ)|^1039 ≤ (13231798673361/100000000000000 : ℝ)^783
        have hw : |(-217792979/1000000000 : ℝ)|=(217792979/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393482451/10000000000 : ℝ)|^1039 ≤ (11019060561879/25000000000000 : ℝ)^783
        have hw : |(5393482451/10000000000 : ℝ)|=(5393482451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632663777/5000000000 : ℝ)|^1039 ≤ (42691959061757/100000000000000 : ℝ)^783
        have hw : |(2632663777/5000000000 : ℝ)|=(2632663777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s7_1 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344846931/10000000000 : ℝ)*x 0 + (-2242938531/10000000000 : ℝ)*x 1 + (5265327563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344846931/10000000000 : ℝ)^1039 ≤ (43549618226937/100000000000000 : ℝ)^783 := by
    have hnat : (5344846931 : ℕ)^1039*100000000000000^783 ≤ 43549618226937^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344846931 10000000000 43549618226937 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242938531/10000000000 : ℝ)^1039 ≤ (6879211302569/50000000000000 : ℝ)^783 := by
    have hnat : (2242938531 : ℕ)^1039*50000000000000^783 ≤ 6879211302569^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242938531 10000000000 6879211302569 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265327563/10000000000 : ℝ)^1039 ≤ (10672989789647/25000000000000 : ℝ)^783 := by
    have hnat : (5265327563 : ℕ)^1039*25000000000000^783 ≤ 10672989789647^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265327563 10000000000 10672989789647 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344846931/10000000000 : ℝ), (-2242938531/10000000000 : ℝ), (5265327563/10000000000 : ℝ)] ![(43549618226937/100000000000000 : ℝ), (6879211302569/50000000000000 : ℝ), (10672989789647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344846931/10000000000 : ℝ)|^1039 ≤ (43549618226937/100000000000000 : ℝ)^783
        have hw : |(5344846931/10000000000 : ℝ)|=(5344846931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2242938531/10000000000 : ℝ)|^1039 ≤ (6879211302569/50000000000000 : ℝ)^783
        have hw : |(-2242938531/10000000000 : ℝ)|=(2242938531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265327563/10000000000 : ℝ)|^1039 ≤ (10672989789647/25000000000000 : ℝ)^783
        have hw : |(5265327563/10000000000 : ℝ)|=(5265327563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s7_2 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672423467/5000000000 : ℝ)*x 0 + (1053065513/2000000000 : ℝ)*x 1 + (-560734631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672423467/5000000000 : ℝ)^1039 ≤ (10887404564843/25000000000000 : ℝ)^783 := by
    have hnat : (2672423467 : ℕ)^1039*25000000000000^783 ≤ 10887404564843^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672423467 5000000000 10887404564843 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053065513/2000000000 : ℝ)^1039 ≤ (42691959180107/100000000000000 : ℝ)^783 := by
    have hnat : (1053065513 : ℕ)^1039*100000000000000^783 ≤ 42691959180107^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053065513 2000000000 42691959180107 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560734631/2500000000 : ℝ)^1039 ≤ (13758422548161/100000000000000 : ℝ)^783 := by
    have hnat : (560734631 : ℕ)^1039*100000000000000^783 ≤ 13758422548161^783*2500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560734631 2500000000 13758422548161 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672423467/5000000000 : ℝ), (1053065513/2000000000 : ℝ), (-560734631/2500000000 : ℝ)] ![(10887404564843/25000000000000 : ℝ), (42691959180107/100000000000000 : ℝ), (13758422548161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672423467/5000000000 : ℝ)|^1039 ≤ (10887404564843/25000000000000 : ℝ)^783
        have hw : |(2672423467/5000000000 : ℝ)|=(2672423467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053065513/2000000000 : ℝ)|^1039 ≤ (42691959180107/100000000000000 : ℝ)^783
        have hw : |(1053065513/2000000000 : ℝ)|=(1053065513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-560734631/2500000000 : ℝ)|^1039 ≤ (13758422548161/100000000000000 : ℝ)^783
        have hw : |(-560734631/2500000000 : ℝ)|=(560734631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s7_3 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (218396083/500000000 : ℝ)*x 0 + (4242860559/10000000000 : ℝ)*x 1 + (562083957/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218396083/500000000 : ℝ)^1039 ≤ (16658410273369/50000000000000 : ℝ)^783 := by
    have hnat : (218396083 : ℕ)^1039*50000000000000^783 ≤ 16658410273369^783*500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218396083 500000000 16658410273369 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242860559/10000000000 : ℝ)^1039 ≤ (32056984702009/100000000000000 : ℝ)^783 := by
    have hnat : (4242860559 : ℕ)^1039*100000000000000^783 ≤ 32056984702009^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242860559 10000000000 32056984702009 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562083957/1250000000 : ℝ)^1039 ≤ (17313097370391/50000000000000 : ℝ)^783 := by
    have hnat : (562083957 : ℕ)^1039*50000000000000^783 ≤ 17313097370391^783*1250000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562083957 1250000000 17313097370391 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218396083/500000000 : ℝ), (4242860559/10000000000 : ℝ), (562083957/1250000000 : ℝ)] ![(16658410273369/50000000000000 : ℝ), (32056984702009/100000000000000 : ℝ), (17313097370391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218396083/500000000 : ℝ)|^1039 ≤ (16658410273369/50000000000000 : ℝ)^783
        have hw : |(218396083/500000000 : ℝ)|=(218396083/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242860559/10000000000 : ℝ)|^1039 ≤ (32056984702009/100000000000000 : ℝ)^783
        have hw : |(4242860559/10000000000 : ℝ)|=(4242860559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562083957/1250000000 : ℝ)|^1039 ≤ (17313097370391/50000000000000 : ℝ)^783
        have hw : |(562083957/1250000000 : ℝ)|=(562083957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s7_4 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-272241841/1250000000 : ℝ)*x 0 + (2632824727/5000000000 : ℝ)*x 1 + (2696579697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272241841/1250000000 : ℝ)^1039 ≤ (1653979810281/12500000000000 : ℝ)^783 := by
    have hnat : (272241841 : ℕ)^1039*12500000000000^783 ≤ 1653979810281^783*1250000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272241841 1250000000 1653979810281 12500000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632824727/5000000000 : ℝ)^1039 ≤ (42695422438953/100000000000000 : ℝ)^783 := by
    have hnat : (2632824727 : ℕ)^1039*100000000000000^783 ≤ 42695422438953^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632824727 5000000000 42695422438953 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696579697/5000000000 : ℝ)^1039 ≤ (11018184763799/25000000000000 : ℝ)^783 := by
    have hnat : (2696579697 : ℕ)^1039*25000000000000^783 ≤ 11018184763799^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696579697 5000000000 11018184763799 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272241841/1250000000 : ℝ), (2632824727/5000000000 : ℝ), (2696579697/5000000000 : ℝ)] ![(1653979810281/12500000000000 : ℝ), (42695422438953/100000000000000 : ℝ), (11018184763799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272241841/1250000000 : ℝ)|^1039 ≤ (1653979810281/12500000000000 : ℝ)^783
        have hw : |(-272241841/1250000000 : ℝ)|=(272241841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632824727/5000000000 : ℝ)|^1039 ≤ (42695422438953/100000000000000 : ℝ)^783
        have hw : |(2632824727/5000000000 : ℝ)|=(2632824727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696579697/5000000000 : ℝ)|^1039 ≤ (11018184763799/25000000000000 : ℝ)^783
        have hw : |(2696579697/5000000000 : ℝ)|=(2696579697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s7_5 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656217083/5000000000 : ℝ)*x 0 + (-2115106697/10000000000 : ℝ)*x 1 + (2696579697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656217083/5000000000 : ℝ)^1039 ≤ (43199521859321/100000000000000 : ℝ)^783 := by
    have hnat : (2656217083 : ℕ)^1039*100000000000000^783 ≤ 43199521859321^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656217083 5000000000 43199521859321 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115106697/10000000000 : ℝ)^1039 ≤ (3181934768479/25000000000000 : ℝ)^783 := by
    have hnat : (2115106697 : ℕ)^1039*25000000000000^783 ≤ 3181934768479^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115106697 10000000000 3181934768479 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696579697/5000000000 : ℝ)^1039 ≤ (11018184763799/25000000000000 : ℝ)^783 := by
    have hnat : (2696579697 : ℕ)^1039*25000000000000^783 ≤ 11018184763799^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696579697 5000000000 11018184763799 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656217083/5000000000 : ℝ), (-2115106697/10000000000 : ℝ), (2696579697/5000000000 : ℝ)] ![(43199521859321/100000000000000 : ℝ), (3181934768479/25000000000000 : ℝ), (11018184763799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656217083/5000000000 : ℝ)|^1039 ≤ (43199521859321/100000000000000 : ℝ)^783
        have hw : |(2656217083/5000000000 : ℝ)|=(2656217083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2115106697/10000000000 : ℝ)|^1039 ≤ (3181934768479/25000000000000 : ℝ)^783
        have hw : |(-2115106697/10000000000 : ℝ)|=(2115106697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696579697/5000000000 : ℝ)|^1039 ≤ (11018184763799/25000000000000 : ℝ)^783
        have hw : |(2696579697/5000000000 : ℝ)|=(2696579697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s7_6 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656217083/5000000000 : ℝ)*x 0 + (2696579697/5000000000 : ℝ)*x 1 + (-2115106697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656217083/5000000000 : ℝ)^1039 ≤ (43199521859321/100000000000000 : ℝ)^783 := by
    have hnat : (2656217083 : ℕ)^1039*100000000000000^783 ≤ 43199521859321^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656217083 5000000000 43199521859321 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696579697/5000000000 : ℝ)^1039 ≤ (11018184763799/25000000000000 : ℝ)^783 := by
    have hnat : (2696579697 : ℕ)^1039*25000000000000^783 ≤ 11018184763799^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696579697 5000000000 11018184763799 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115106697/10000000000 : ℝ)^1039 ≤ (3181934768479/25000000000000 : ℝ)^783 := by
    have hnat : (2115106697 : ℕ)^1039*25000000000000^783 ≤ 3181934768479^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115106697 10000000000 3181934768479 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656217083/5000000000 : ℝ), (2696579697/5000000000 : ℝ), (-2115106697/10000000000 : ℝ)] ![(43199521859321/100000000000000 : ℝ), (11018184763799/25000000000000 : ℝ), (3181934768479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656217083/5000000000 : ℝ)|^1039 ≤ (43199521859321/100000000000000 : ℝ)^783
        have hw : |(2656217083/5000000000 : ℝ)|=(2656217083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696579697/5000000000 : ℝ)|^1039 ≤ (11018184763799/25000000000000 : ℝ)^783
        have hw : |(2696579697/5000000000 : ℝ)|=(2696579697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2115106697/10000000000 : ℝ)|^1039 ≤ (3181934768479/25000000000000 : ℝ)^783
        have hw : |(-2115106697/10000000000 : ℝ)|=(2115106697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s7_7 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (873586291/2000000000 : ℝ)*x 0 + (4496034167/10000000000 : ℝ)*x 1 + (4243500353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873586291/2000000000 : ℝ)^1039 ≤ (33316919686323/100000000000000 : ℝ)^783 := by
    have hnat : (873586291 : ℕ)^1039*100000000000000^783 ≤ 33316919686323^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873586291 2000000000 33316919686323 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496034167/10000000000 : ℝ)^1039 ≤ (17309840503493/50000000000000 : ℝ)^783 := by
    have hnat : (4496034167 : ℕ)^1039*50000000000000^783 ≤ 17309840503493^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496034167 10000000000 17309840503493 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4243500353/10000000000 : ℝ)^1039 ≤ (32063399287013/100000000000000 : ℝ)^783 := by
    have hnat : (4243500353 : ℕ)^1039*100000000000000^783 ≤ 32063399287013^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243500353 10000000000 32063399287013 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873586291/2000000000 : ℝ), (4496034167/10000000000 : ℝ), (4243500353/10000000000 : ℝ)] ![(33316919686323/100000000000000 : ℝ), (17309840503493/50000000000000 : ℝ), (32063399287013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873586291/2000000000 : ℝ)|^1039 ≤ (33316919686323/100000000000000 : ℝ)^783
        have hw : |(873586291/2000000000 : ℝ)|=(873586291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496034167/10000000000 : ℝ)|^1039 ≤ (17309840503493/50000000000000 : ℝ)^783
        have hw : |(4496034167/10000000000 : ℝ)|=(4496034167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4243500353/10000000000 : ℝ)|^1039 ≤ (32063399287013/100000000000000 : ℝ)^783
        have hw : |(4243500353/10000000000 : ℝ)|=(4243500353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1119_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5661/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14037/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3511/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2263/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3511/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2263/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3511/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2263/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3511/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2263/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3511/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2263/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3511/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2263/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2263/20000 : ℝ) ^ (8311/2048 : ℝ) ≤ (3610525331392519/25000000000000000000 : ℝ) := by
    have hpowers : (2263/20000 : ℝ)^8311 ≤ (3610525331392519/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2263 : ℕ)^8311*25000000000000000000^2048 ≤ 3610525331392519^2048*20000^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2263 20000 3610525331392519 25000000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2263/20000 : ℝ)) (X := (3610525331392519/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3511/25000 : ℝ) ^ (8311/2048 : ℝ) ≤ (34707860057414699/100000000000000000000 : ℝ) := by
    have hpowers : (3511/25000 : ℝ)^8311 ≤ (34707860057414699/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3511 : ℕ)^8311*100000000000000000000^2048 ≤ 34707860057414699^2048*25000^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3511 25000 34707860057414699 100000000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3511/25000 : ℝ)) (X := (34707860057414699/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503610525331392519/12500000000000000000 : ℝ) ≤ (2000142337649219/2000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (12503610525331392519/12500000000000000000 : ℝ)^2048 ≤ (2000142337649219/2000000000000000 : ℝ)^8311 := by
      have hnat : (12503610525331392519 : ℕ)^2048*2000000000000000^8311 ≤ 2000142337649219^8311*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503610525331392519 12500000000000000000 2000142337649219 2000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000142337649219/2000000000000000 : ℝ)) (X := (12503610525331392519/12500000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001965998455319391/4000000000000000000 : ℝ) ≤ (1250151366389421/1250000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (4001965998455319391/4000000000000000000 : ℝ)^2048 ≤ (1250151366389421/1250000000000000 : ℝ)^8311 := by
      have hnat : (4001965998455319391 : ℕ)^2048*1250000000000000^8311 ≤ 1250151366389421^8311*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001965998455319391 4000000000000000000 1250151366389421 1250000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250151366389421/1250000000000000 : ℝ)) (X := (4001965998455319391/4000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034707860057414699/50000000000000000000 : ℝ) ≤ (10001710173984641/10000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (50034707860057414699/50000000000000000000 : ℝ)^2048 ≤ (10001710173984641/10000000000000000 : ℝ)^8311 := by
      have hnat : (50034707860057414699 : ℕ)^2048*10000000000000000^8311 ≤ 10001710173984641^8311*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034707860057414699 50000000000000000000 10001710173984641 10000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001710173984641/10000000000000000 : ℝ)) (X := (50034707860057414699/50000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3610525331392519/25000000000000000000 : ℝ) ≤ ((5456128866218389053/5458000000000000000 : ℝ)+2*(499242869273/272900000000000 : ℝ)*(2263/20000 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (5456128866218389053/5458000000000000000 : ℝ)+2*(499242869273/272900000000000 : ℝ)*(2263/20000 : ℝ)=(2000142337649219/2000000000000000 : ℝ) by norm_num, show 1+2*(3610525331392519/25000000000000000000 : ℝ)=(12503610525331392519/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34707860057414699/100000000000000000000 : ℝ)+(3610525331392519/25000000000000000000 : ℝ) ≤ ((5456128866218389053/5458000000000000000 : ℝ)+(499242869273/272900000000000 : ℝ)*((3511/25000 : ℝ)+(2263/20000 : ℝ)))^(8311/2048 : ℝ) := by
    rw [show (5456128866218389053/5458000000000000000 : ℝ)+(499242869273/272900000000000 : ℝ)*((3511/25000 : ℝ)+(2263/20000 : ℝ))=(1250151366389421/1250000000000000 : ℝ) by norm_num, show 1+(34707860057414699/100000000000000000000 : ℝ)+(3610525331392519/25000000000000000000 : ℝ)=(4001965998455319391/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34707860057414699/100000000000000000000 : ℝ) ≤ ((5456128866218389053/5458000000000000000 : ℝ)+2*(499242869273/272900000000000 : ℝ)*(3511/25000 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (5456128866218389053/5458000000000000000 : ℝ)+2*(499242869273/272900000000000 : ℝ)*(3511/25000 : ℝ)=(10001710173984641/10000000000000000 : ℝ) by norm_num, show 1+2*(34707860057414699/100000000000000000000 : ℝ)=(50034707860057414699/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5456128866218389053/5458000000000000000 : ℝ)*(X 1 0+X 2 0)+(499242869273/272900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (5456128866218389053/5458000000000000000 : ℝ)) (alpha := (499242869273/272900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5456128866218389053/5458000000000000000 : ℝ)*(X 0 1+X 2 1)+(499242869273/272900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (5456128866218389053/5458000000000000000 : ℝ)) (alpha := (499242869273/272900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5456128866218389053/5458000000000000000 : ℝ)*(X 0 2+X 1 2)+(499242869273/272900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (5456128866218389053/5458000000000000000 : ℝ)) (alpha := (499242869273/272900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-217792979/1000000000 : ℝ)*X 0 0+(5393482451/10000000000 : ℝ)*X 0 1+(2632663777/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344846931/10000000000 : ℝ)*X 1 0+(-2242938531/10000000000 : ℝ)*X 1 1+(5265327563/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672423467/5000000000 : ℝ)*X 2 0+(1053065513/2000000000 : ℝ)*X 2 1+(-560734631/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218396083/500000000 : ℝ)*X 0 0+(4242860559/10000000000 : ℝ)*X 0 1+(562083957/1250000000 : ℝ)*X 0 2+(218396083/500000000 : ℝ)*X 1 0+(4242860559/10000000000 : ℝ)*X 1 1+(562083957/1250000000 : ℝ)*X 1 2+(218396083/500000000 : ℝ)*X 2 0+(4242860559/10000000000 : ℝ)*X 2 1+(562083957/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-272241841/1250000000 : ℝ)*X 0 0+(2632824727/5000000000 : ℝ)*X 0 1+(2696579697/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656217083/5000000000 : ℝ)*X 1 0+(-2115106697/10000000000 : ℝ)*X 1 1+(2696579697/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656217083/5000000000 : ℝ)*X 2 0+(2696579697/5000000000 : ℝ)*X 2 1+(-2115106697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873586291/2000000000 : ℝ)*X 0 0+(4496034167/10000000000 : ℝ)*X 0 1+(4243500353/10000000000 : ℝ)*X 0 2+(873586291/2000000000 : ℝ)*X 1 0+(4496034167/10000000000 : ℝ)*X 1 1+(4243500353/10000000000 : ℝ)*X 1 2+(873586291/2000000000 : ℝ)*X 2 0+(4496034167/10000000000 : ℝ)*X 2 1+(4243500353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (363118109404600341552610407/54580000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1332495833/100000000000000 : ℝ)*(base19) + (1257009059/100000000000000 : ℝ)*(base23) + (5335933/12500000000000 : ℝ)*(lower2) + (162305619/100000000000000 : ℝ)*(upper3) + (11481757/10000000000000 : ℝ)*(upper5) + (1174310805184273/20000000000000 : ℝ)*(major0) + (1174310805184273/20000000000000 : ℝ)*(major1) + (1174310805184273/20000000000000 : ℝ)*(major2) + (975386915187787/12500000000000 : ℝ)*(sp0) + (975391399367841/12500000000000 : ℝ)*(sp1) + (3901565635214751/50000000000000 : ℝ)*(sp2) + (1969977960389771/50000000000000 : ℝ)*(sp3) + (7441187253/20000000000000 : ℝ)*(sp4) + (9690929779/50000000000000 : ℝ)*(sp7) + (3939975302639099/100000000000000 : ℝ)*(f.failure) + (7803132527438561/100000000000000 : ℝ)*(f.sum) + (27792542319121/2729000000000000000000000000 : ℝ)*base66 + (609835332576343469/109160000000000000000000000000000 : ℝ)*base67 + (1215375970205656531/109160000000000000000000000000000 : ℝ)*base70 + (1334171682560936531/109160000000000000000000000000000 : ℝ)*base72 + (2841833580791/545800000000000000000000000 : ℝ)*base74 + (1651112613350856531/109160000000000000000000000000000 : ℝ)*base76 + (2006191109116936531/109160000000000000000000000000000 : ℝ)*base78 + (557267607228503469/109160000000000000000000000000000 : ℝ)*base79 + (11380834710933/2729000000000000000000000000 : ℝ)*base82 + (4765413/2500000000000000000000 : ℝ)*base89 + (4765413/2500000000000000000000 : ℝ)*base91 + (4765413/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69256793288914058514441/6822500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1866356347/100000000000000 : ℝ)*(base19) + (405856047/20000000000000 : ℝ)*(base23) + (12748439/6250000000000 : ℝ)*(upper3) + (231577/312500000000 : ℝ)*(lower4) + (10370251/5000000000000 : ℝ)*(upper5) + (2950597362058531/50000000000000 : ℝ)*(major0) + (2950597362058531/50000000000000 : ℝ)*(major1) + (2950597362058531/50000000000000 : ℝ)*(major2) + (25651889473/50000000000000 : ℝ)*(sp1) + (55144113443/100000000000000 : ℝ)*(sp2) + (3921262039071137/50000000000000 : ℝ)*(sp4) + (3921235454003491/50000000000000 : ℝ)*(sp5) + (3921233452374299/50000000000000 : ℝ)*(sp6) + (3959865031717373/100000000000000 : ℝ)*(sp7) + (3959865031717373/100000000000000 : ℝ)*(f.failure) + (3921262039071137/50000000000000 : ℝ)*(f.sum) + (89411904999809/13645000000000000000000000000 : ℝ)*base66 + (2996867124692621143/272900000000000000000000000000000 : ℝ)*base67 + (79549022087578857/272900000000000000000000000000000 : ℝ)*base70 + (4141713232648778857/272900000000000000000000000000000 : ℝ)*base72 + (138085991243331/13645000000000000000000000000 : ℝ)*base73 + (8071385728317421143/272900000000000000000000000000000 : ℝ)*base75 + (4482475628235578857/272900000000000000000000000000000 : ℝ)*base78 + (4360120650940721143/272900000000000000000000000000000 : ℝ)*base79 + (9754258376431/13645000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base87 + (1374051/2500000000000000000000 : ℝ)*base89 + (1374051/2500000000000000000000 : ℝ)*base91 + (1374051/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1119_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1119_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1119_s8_0 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1088967407/5000000000 : ℝ)*x 0 + (1078682151/2000000000 : ℝ)*x 1 + (5265396051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088967407/5000000000 : ℝ)^1039 ≤ (6615919587779/50000000000000 : ℝ)^783 := by
    have hnat : (1088967407 : ℕ)^1039*50000000000000^783 ≤ 6615919587779^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088967407 5000000000 6615919587779 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078682151/2000000000 : ℝ)^1039 ≤ (8815092955711/20000000000000 : ℝ)^783 := by
    have hnat : (1078682151 : ℕ)^1039*20000000000000^783 ≤ 8815092955711^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078682151 2000000000 8815092955711 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265396051/10000000000 : ℝ)^1039 ≤ (21346348013453/50000000000000 : ℝ)^783 := by
    have hnat : (5265396051 : ℕ)^1039*50000000000000^783 ≤ 21346348013453^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265396051 10000000000 21346348013453 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1088967407/5000000000 : ℝ), (1078682151/2000000000 : ℝ), (5265396051/10000000000 : ℝ)] ![(6615919587779/50000000000000 : ℝ), (8815092955711/20000000000000 : ℝ), (21346348013453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1088967407/5000000000 : ℝ)|^1039 ≤ (6615919587779/50000000000000 : ℝ)^783
        have hw : |(-1088967407/5000000000 : ℝ)|=(1088967407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078682151/2000000000 : ℝ)|^1039 ≤ (8815092955711/20000000000000 : ℝ)^783
        have hw : |(1078682151/2000000000 : ℝ)|=(1078682151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265396051/10000000000 : ℝ)|^1039 ≤ (21346348013453/50000000000000 : ℝ)^783
        have hw : |(5265396051/10000000000 : ℝ)|=(5265396051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s8_1 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (53448293/100000000 : ℝ)*x 0 + (-560718053/2500000000 : ℝ)*x 1 + (1316348863/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53448293/100000000 : ℝ)^1039 ≤ (43549427602059/100000000000000 : ℝ)^783 := by
    have hnat : (53448293 : ℕ)^1039*100000000000000^783 ≤ 43549427602059^783*100000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53448293 100000000 43549427602059 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560718053/2500000000 : ℝ)^1039 ≤ (6878941397567/50000000000000 : ℝ)^783 := by
    have hnat : (560718053 : ℕ)^1039*50000000000000^783 ≤ 6878941397567^783*2500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560718053 2500000000 6878941397567 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316348863/2500000000 : ℝ)^1039 ≤ (213463447911/500000000000 : ℝ)^783 := by
    have hnat : (1316348863 : ℕ)^1039*500000000000^783 ≤ 213463447911^783*2500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316348863 2500000000 213463447911 500000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53448293/100000000 : ℝ), (-560718053/2500000000 : ℝ), (1316348863/2500000000 : ℝ)] ![(43549427602059/100000000000000 : ℝ), (6878941397567/50000000000000 : ℝ), (213463447911/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53448293/100000000 : ℝ)|^1039 ≤ (43549427602059/100000000000000 : ℝ)^783
        have hw : |(53448293/100000000 : ℝ)|=(53448293/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560718053/2500000000 : ℝ)|^1039 ≤ (6878941397567/50000000000000 : ℝ)^783
        have hw : |(-560718053/2500000000 : ℝ)|=(560718053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316348863/2500000000 : ℝ)|^1039 ≤ (213463447911/500000000000 : ℝ)^783
        have hw : |(1316348863/2500000000 : ℝ)|=(1316348863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s8_2 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672415007/5000000000 : ℝ)*x 0 + (5265394713/10000000000 : ℝ)*x 1 + (-1121436121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672415007/5000000000 : ℝ)^1039 ≤ (43549435321763/100000000000000 : ℝ)^783 := by
    have hnat : (2672415007 : ℕ)^1039*100000000000000^783 ≤ 43549435321763^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672415007 5000000000 43549435321763 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265394713/10000000000 : ℝ)^1039 ≤ (21346340815609/50000000000000 : ℝ)^783 := by
    have hnat : (5265394713 : ℕ)^1039*50000000000000^783 ≤ 21346340815609^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265394713 10000000000 21346340815609 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121436121/5000000000 : ℝ)^1039 ≤ (13757883039321/100000000000000 : ℝ)^783 := by
    have hnat : (1121436121 : ℕ)^1039*100000000000000^783 ≤ 13757883039321^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121436121 5000000000 13757883039321 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672415007/5000000000 : ℝ), (5265394713/10000000000 : ℝ), (-1121436121/5000000000 : ℝ)] ![(43549435321763/100000000000000 : ℝ), (21346340815609/50000000000000 : ℝ), (13757883039321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672415007/5000000000 : ℝ)|^1039 ≤ (43549435321763/100000000000000 : ℝ)^783
        have hw : |(2672415007/5000000000 : ℝ)|=(2672415007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265394713/10000000000 : ℝ)|^1039 ≤ (21346340815609/50000000000000 : ℝ)^783
        have hw : |(5265394713/10000000000 : ℝ)|=(5265394713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1121436121/5000000000 : ℝ)|^1039 ≤ (13757883039321/100000000000000 : ℝ)^783
        have hw : |(-1121436121/5000000000 : ℝ)|=(1121436121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s8_3 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4367925209/10000000000 : ℝ)*x 0 + (2121499377/5000000000 : ℝ)*x 1 + (70258321/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367925209/10000000000 : ℝ)^1039 ≤ (33316856467749/100000000000000 : ℝ)^783 := by
    have hnat : (4367925209 : ℕ)^1039*100000000000000^783 ≤ 33316856467749^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367925209 10000000000 33316856467749 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121499377/5000000000 : ℝ)^1039 ≤ (32058370220541/100000000000000 : ℝ)^783 := by
    have hnat : (2121499377 : ℕ)^1039*100000000000000^783 ≤ 32058370220541^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121499377 5000000000 32058370220541 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70258321/156250000 : ℝ)^1039 ≤ (34624773296719/100000000000000 : ℝ)^783 := by
    have hnat : (70258321 : ℕ)^1039*100000000000000^783 ≤ 34624773296719^783*156250000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70258321 156250000 34624773296719 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367925209/10000000000 : ℝ), (2121499377/5000000000 : ℝ), (70258321/156250000 : ℝ)] ![(33316856467749/100000000000000 : ℝ), (32058370220541/100000000000000 : ℝ), (34624773296719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367925209/10000000000 : ℝ)|^1039 ≤ (33316856467749/100000000000000 : ℝ)^783
        have hw : |(4367925209/10000000000 : ℝ)|=(4367925209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2121499377/5000000000 : ℝ)|^1039 ≤ (32058370220541/100000000000000 : ℝ)^783
        have hw : |(2121499377/5000000000 : ℝ)|=(2121499377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70258321/156250000 : ℝ)|^1039 ≤ (34624773296719/100000000000000 : ℝ)^783
        have hw : |(70258321/156250000 : ℝ)|=(70258321/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s8_4 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2177939797/10000000000 : ℝ)*x 0 + (1053143343/2000000000 : ℝ)*x 1 + (5393088889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177939797/10000000000 : ℝ)^1039 ≤ (2646375869451/20000000000000 : ℝ)^783 := by
    have hnat : (2177939797 : ℕ)^1039*20000000000000^783 ≤ 2646375869451^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177939797 10000000000 2646375869451 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053143343/2000000000 : ℝ)^1039 ≤ (10674036530077/25000000000000 : ℝ)^783 := by
    have hnat : (1053143343 : ℕ)^1039*25000000000000^783 ≤ 10674036530077^783*2000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053143343 2000000000 10674036530077 25000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393088889/10000000000 : ℝ)^1039 ≤ (5508996814543/12500000000000 : ℝ)^783 := by
    have hnat : (5393088889 : ℕ)^1039*12500000000000^783 ≤ 5508996814543^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393088889 10000000000 5508996814543 12500000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2177939797/10000000000 : ℝ), (1053143343/2000000000 : ℝ), (5393088889/10000000000 : ℝ)] ![(2646375869451/20000000000000 : ℝ), (10674036530077/25000000000000 : ℝ), (5508996814543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2177939797/10000000000 : ℝ)|^1039 ≤ (2646375869451/20000000000000 : ℝ)^783
        have hw : |(-2177939797/10000000000 : ℝ)|=(2177939797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053143343/2000000000 : ℝ)|^1039 ≤ (10674036530077/25000000000000 : ℝ)^783
        have hw : |(1053143343/2000000000 : ℝ)|=(1053143343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393088889/10000000000 : ℝ)|^1039 ≤ (5508996814543/12500000000000 : ℝ)^783
        have hw : |(5393088889/10000000000 : ℝ)|=(5393088889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s8_5 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312452013/10000000000 : ℝ)*x 0 + (-1057589139/5000000000 : ℝ)*x 1 + (1348272231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312452013/10000000000 : ℝ)^1039 ≤ (21599857218207/50000000000000 : ℝ)^783 := by
    have hnat : (5312452013 : ℕ)^1039*50000000000000^783 ≤ 21599857218207^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312452013 10000000000 21599857218207 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057589139/5000000000 : ℝ)^1039 ≤ (12728310648531/100000000000000 : ℝ)^783 := by
    have hnat : (1057589139 : ℕ)^1039*100000000000000^783 ≤ 12728310648531^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057589139 5000000000 12728310648531 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348272231/2500000000 : ℝ)^1039 ≤ (22035987447937/50000000000000 : ℝ)^783 := by
    have hnat : (1348272231 : ℕ)^1039*50000000000000^783 ≤ 22035987447937^783*2500000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348272231 2500000000 22035987447937 50000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312452013/10000000000 : ℝ), (-1057589139/5000000000 : ℝ), (1348272231/2500000000 : ℝ)] ![(21599857218207/50000000000000 : ℝ), (12728310648531/100000000000000 : ℝ), (22035987447937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312452013/10000000000 : ℝ)|^1039 ≤ (21599857218207/50000000000000 : ℝ)^783
        have hw : |(5312452013/10000000000 : ℝ)|=(5312452013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1057589139/5000000000 : ℝ)|^1039 ≤ (12728310648531/100000000000000 : ℝ)^783
        have hw : |(-1057589139/5000000000 : ℝ)|=(1057589139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348272231/2500000000 : ℝ)|^1039 ≤ (22035987447937/50000000000000 : ℝ)^783
        have hw : |(1348272231/2500000000 : ℝ)|=(1348272231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s8_6 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312451277/10000000000 : ℝ)*x 0 + (2696544389/5000000000 : ℝ)*x 1 + (-2115179471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312451277/10000000000 : ℝ)^1039 ≤ (43199706494641/100000000000000 : ℝ)^783 := by
    have hnat : (5312451277 : ℕ)^1039*100000000000000^783 ≤ 43199706494641^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312451277 10000000000 43199706494641 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696544389/5000000000 : ℝ)^1039 ≤ (4407197331269/10000000000000 : ℝ)^783 := by
    have hnat : (2696544389 : ℕ)^1039*10000000000000^783 ≤ 4407197331269^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696544389 5000000000 4407197331269 10000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115179471/10000000000 : ℝ)^1039 ≤ (2545664034939/20000000000000 : ℝ)^783 := by
    have hnat : (2115179471 : ℕ)^1039*20000000000000^783 ≤ 2545664034939^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115179471 10000000000 2545664034939 20000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312451277/10000000000 : ℝ), (2696544389/5000000000 : ℝ), (-2115179471/10000000000 : ℝ)] ![(43199706494641/100000000000000 : ℝ), (4407197331269/10000000000000 : ℝ), (2545664034939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312451277/10000000000 : ℝ)|^1039 ≤ (43199706494641/100000000000000 : ℝ)^783
        have hw : |(5312451277/10000000000 : ℝ)|=(5312451277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696544389/5000000000 : ℝ)|^1039 ≤ (4407197331269/10000000000000 : ℝ)^783
        have hw : |(2696544389/5000000000 : ℝ)|=(2696544389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2115179471/10000000000 : ℝ)|^1039 ≤ (2545664034939/20000000000000 : ℝ)^783
        have hw : |(-2115179471/10000000000 : ℝ)|=(2115179471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1119_s8_7 (p : ℝ) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ)) (x : Fin 3 → ℝ) :
    (27299589/62500000 : ℝ)*x 0 + (2247948547/5000000000 : ℝ)*x 1 + (4243637229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27299589/62500000 : ℝ)^1039 ≤ (33316947874569/100000000000000 : ℝ)^783 := by
    have hnat : (27299589 : ℕ)^1039*100000000000000^783 ≤ 33316947874569^783*62500000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27299589 62500000 33316947874569 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247948547/5000000000 : ℝ)^1039 ≤ (34618280462211/100000000000000 : ℝ)^783 := by
    have hnat : (2247948547 : ℕ)^1039*100000000000000^783 ≤ 34618280462211^783*5000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247948547 5000000000 34618280462211 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4243637229/10000000000 : ℝ)^1039 ≤ (32064771649067/100000000000000 : ℝ)^783 := by
    have hnat : (4243637229 : ℕ)^1039*100000000000000^783 ≤ 32064771649067^783*10000000000^1039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243637229 10000000000 32064771649067 100000000000000 1039 783 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1039/256 : ℝ)) 1039 783 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27299589/62500000 : ℝ), (2247948547/5000000000 : ℝ), (4243637229/10000000000 : ℝ)] ![(33316947874569/100000000000000 : ℝ), (34618280462211/100000000000000 : ℝ), (32064771649067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27299589/62500000 : ℝ)|^1039 ≤ (33316947874569/100000000000000 : ℝ)^783
        have hw : |(27299589/62500000 : ℝ)|=(27299589/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247948547/5000000000 : ℝ)|^1039 ≤ (34618280462211/100000000000000 : ℝ)^783
        have hw : |(2247948547/5000000000 : ℝ)|=(2247948547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4243637229/10000000000 : ℝ)|^1039 ≤ (32064771649067/100000000000000 : ℝ)^783
        have hw : |(4243637229/10000000000 : ℝ)|=(4243637229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1119_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11323/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2807/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14037/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14037/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14037/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14037/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14037/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5661/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14037/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5661/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5661/50000 : ℝ) ^ (8311/2048 : ℝ) ≤ (14478393082895681/100000000000000000000 : ℝ) := by
    have hpowers : (5661/50000 : ℝ)^8311 ≤ (14478393082895681/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5661 : ℕ)^8311*100000000000000000000^2048 ≤ 14478393082895681^2048*50000^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5661 50000 14478393082895681 100000000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5661/50000 : ℝ)) (X := (14478393082895681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14037/100000 : ℝ) ^ (8311/2048 : ℝ) ≤ (34637710104371583/100000000000000000000 : ℝ) := by
    have hpowers : (14037/100000 : ℝ)^8311 ≤ (34637710104371583/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14037 : ℕ)^8311*100000000000000000000^2048 ≤ 34637710104371583^2048*100000^8311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14037 100000 34637710104371583 100000000000000000000 8311 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14037/100000 : ℝ)) (X := (34637710104371583/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014478393082895681/50000000000000000000 : ℝ) ≤ (5000356738231153/5000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (50014478393082895681/50000000000000000000 : ℝ)^2048 ≤ (5000356738231153/5000000000000000 : ℝ)^8311 := by
      have hnat : (50014478393082895681 : ℕ)^2048*5000000000000000^8311 ≤ 5000356738231153^8311*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014478393082895681 50000000000000000000 5000356738231153 5000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000356738231153/5000000000000000 : ℝ)) (X := (50014478393082895681/50000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563267439112301051/1562500000000000000 : ℝ) ≤ (10001210097089117/10000000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (1563267439112301051/1562500000000000000 : ℝ)^2048 ≤ (10001210097089117/10000000000000000 : ℝ)^8311 := by
      have hnat : (1563267439112301051 : ℕ)^2048*10000000000000000^8311 ≤ 10001210097089117^8311*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563267439112301051 1562500000000000000 10001210097089117 10000000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001210097089117/10000000000000000 : ℝ)) (X := (1563267439112301051/1562500000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034637710104371583/50000000000000000000 : ℝ) ≤ (1250213339714491/1250000000000000 : ℝ) ^ (8311/2048 : ℝ) := by
    have hpowers : (50034637710104371583/50000000000000000000 : ℝ)^2048 ≤ (1250213339714491/1250000000000000 : ℝ)^8311 := by
      have hnat : (50034637710104371583 : ℕ)^2048*1250000000000000^8311 ≤ 1250213339714491^8311*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034637710104371583 50000000000000000000 1250213339714491 1250000000000000 2048 8311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250213339714491/1250000000000000 : ℝ)) (X := (50034637710104371583/50000000000000000000 : ℝ)) (by norm_num) 8311 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14478393082895681/100000000000000000000 : ℝ) ≤ ((4523448601853608751/4525000000000000000 : ℝ)+2*(165540208937/90500000000000 : ℝ)*(5661/50000 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (4523448601853608751/4525000000000000000 : ℝ)+2*(165540208937/90500000000000 : ℝ)*(5661/50000 : ℝ)=(5000356738231153/5000000000000000 : ℝ) by norm_num, show 1+2*(14478393082895681/100000000000000000000 : ℝ)=(50014478393082895681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34637710104371583/100000000000000000000 : ℝ)+(14478393082895681/100000000000000000000 : ℝ) ≤ ((4523448601853608751/4525000000000000000 : ℝ)+(165540208937/90500000000000 : ℝ)*((14037/100000 : ℝ)+(5661/50000 : ℝ)))^(8311/2048 : ℝ) := by
    rw [show (4523448601853608751/4525000000000000000 : ℝ)+(165540208937/90500000000000 : ℝ)*((14037/100000 : ℝ)+(5661/50000 : ℝ))=(10001210097089117/10000000000000000 : ℝ) by norm_num, show 1+(34637710104371583/100000000000000000000 : ℝ)+(14478393082895681/100000000000000000000 : ℝ)=(1563267439112301051/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34637710104371583/100000000000000000000 : ℝ) ≤ ((4523448601853608751/4525000000000000000 : ℝ)+2*(165540208937/90500000000000 : ℝ)*(14037/100000 : ℝ))^(8311/2048 : ℝ) := by
    rw [show (4523448601853608751/4525000000000000000 : ℝ)+2*(165540208937/90500000000000 : ℝ)*(14037/100000 : ℝ)=(1250213339714491/1250000000000000 : ℝ) by norm_num, show 1+2*(34637710104371583/100000000000000000000 : ℝ)=(50034637710104371583/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4523448601853608751/4525000000000000000 : ℝ)*(X 1 0+X 2 0)+(165540208937/90500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (14037/100000 : ℝ)) (c := (4523448601853608751/4525000000000000000 : ℝ)) (alpha := (165540208937/90500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4523448601853608751/4525000000000000000 : ℝ)*(X 0 1+X 2 1)+(165540208937/90500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (14037/100000 : ℝ)) (c := (4523448601853608751/4525000000000000000 : ℝ)) (alpha := (165540208937/90500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4523448601853608751/4525000000000000000 : ℝ)*(X 0 2+X 1 2)+(165540208937/90500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8311/2048 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (14037/100000 : ℝ)) (c := (4523448601853608751/4525000000000000000 : ℝ)) (alpha := (165540208937/90500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1088967407/5000000000 : ℝ)*X 0 0+(1078682151/2000000000 : ℝ)*X 0 1+(5265396051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53448293/100000000 : ℝ)*X 1 0+(-560718053/2500000000 : ℝ)*X 1 1+(1316348863/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672415007/5000000000 : ℝ)*X 2 0+(5265394713/10000000000 : ℝ)*X 2 1+(-1121436121/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4367925209/10000000000 : ℝ)*X 0 0+(2121499377/5000000000 : ℝ)*X 0 1+(70258321/156250000 : ℝ)*X 0 2+(4367925209/10000000000 : ℝ)*X 1 0+(2121499377/5000000000 : ℝ)*X 1 1+(70258321/156250000 : ℝ)*X 1 2+(4367925209/10000000000 : ℝ)*X 2 0+(2121499377/5000000000 : ℝ)*X 2 1+(70258321/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2177939797/10000000000 : ℝ)*X 0 0+(1053143343/2000000000 : ℝ)*X 0 1+(5393088889/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312452013/10000000000 : ℝ)*X 1 0+(-1057589139/5000000000 : ℝ)*X 1 1+(1348272231/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312451277/10000000000 : ℝ)*X 2 0+(2696544389/5000000000 : ℝ)*X 2 1+(-2115179471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((27299589/62500000 : ℝ)*X 0 0+(2247948547/5000000000 : ℝ)*X 0 1+(4243637229/10000000000 : ℝ)*X 0 2+(27299589/62500000 : ℝ)*X 1 0+(2247948547/5000000000 : ℝ)*X 1 1+(4243637229/10000000000 : ℝ)*X 1 2+(27299589/62500000 : ℝ)*X 2 0+(2247948547/5000000000 : ℝ)*X 2 1+(4243637229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1119_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136978745000351985884395947/14140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (259932531/12500000000000 : ℝ)*(base19) + (2777030161/100000000000000 : ℝ)*(base23) + (184911873/100000000000000 : ℝ)*(lower2) + (38259781/20000000000000 : ℝ)*(upper3) + (16610561/20000000000000 : ℝ)*(upper5) + (734744702838649/12500000000000 : ℝ)*(major0) + (734744702838649/12500000000000 : ℝ)*(major1) + (734744702838649/12500000000000 : ℝ)*(major2) + (3905808575967101/50000000000000 : ℝ)*(sp0) + (3905820274848651/50000000000000 : ℝ)*(sp1) + (1952909963031847/25000000000000 : ℝ)*(sp2) + (986063765259843/25000000000000 : ℝ)*(sp3) + (6369305837/25000000000000 : ℝ)*(sp4) + (8616162481/50000000000000 : ℝ)*(sp7) + (1972136146682167/50000000000000 : ℝ)*(f.failure) + (7811642629157549/100000000000000 : ℝ)*(f.sum) + (2197806955049/1131250000000000000000000000 : ℝ)*base66 + (946510798968807601/56562500000000000000000000000000 : ℝ)*base68 + (842059211160682601/56562500000000000000000000000000 : ℝ)*base70 + (431445263263182601/56562500000000000000000000000000 : ℝ)*base72 + (3677575165651/1131250000000000000000000000 : ℝ)*base73 + (1353081818420057601/56562500000000000000000000000000 : ℝ)*base76 + (955964870948182601/56562500000000000000000000000000 : ℝ)*base78 + (122141747333067399/56562500000000000000000000000000 : ℝ)*base79 + (4514236617673/2262500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (11533929/1250000000000000000000 : ℝ)*base89 + (11533929/1250000000000000000000 : ℝ)*base91 + (11533929/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (450326350856526068588103237/56562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81947681/12500000000000 : ℝ)*(base19) + (160675943/100000000000000 : ℝ)*(upper1) + (36283727/12500000000000 : ℝ)*(upper2) + (131105891/100000000000000 : ℝ)*(lower4) + (7787109/20000000000000 : ℝ)*(lower5) + (1476899331469943/25000000000000 : ℝ)*(major0) + (1476899331469943/25000000000000 : ℝ)*(major1) + (1476899331469943/25000000000000 : ℝ)*(major2) + (5214170753/25000000000000 : ℝ)*(sp0) + (11848687233/20000000000000 : ℝ)*(sp1) + (392550608746881/5000000000000 : ℝ)*(sp4) + (7850973132603019/100000000000000 : ℝ)*(sp5) + (981379128952579/12500000000000 : ℝ)*(sp6) + (495520169344151/12500000000000 : ℝ)*(sp7) + (495520169344151/12500000000000 : ℝ)*(f.failure) + (981379128952579/12500000000000 : ℝ)*(f.sum) + (2465588575867/565625000000000000000000000 : ℝ)*base66 + (461817611227178807/113125000000000000000000000000000 : ℝ)*base68 + (2042262156647178807/113125000000000000000000000000000 : ℝ)*base70 + (902316604761553807/113125000000000000000000000000000 : ℝ)*base72 + (2154664942557/2262500000000000000000000000 : ℝ)*base73 + (2954897341187178807/113125000000000000000000000000000 : ℝ)*base76 + (1610466131247178807/113125000000000000000000000000000 : ℝ)*base78 + (385973558612178807/113125000000000000000000000000000 : ℝ)*base80 + (320355942909/1131250000000000000000000000 : ℝ)*base82 + (3927337/312500000000000000000 : ℝ)*base89 + (3927337/312500000000000000000 : ℝ)*base91 + (3927337/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1119_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1119_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1119_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1119_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1119_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1119_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8311/2048 : ℝ) ≤ p) (hpb : p ≤ (1039/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37256287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11323/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1119_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

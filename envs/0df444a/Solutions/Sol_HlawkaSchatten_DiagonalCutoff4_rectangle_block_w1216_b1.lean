-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1216_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:08:59.647806+00:00
-- url     : https://prove2.me/submissions/a31e6895-1490-4f46-8577-7e50b87c884a

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
theorem support_rectangle_w1216_s3_0 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128925453/10000000000 : ℝ)*x 0 + (542198541/1000000000 : ℝ)*x 1 + (209542507/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128925453/10000000000 : ℝ)^8409 ≤ (6468799414149/50000000000000 : ℝ)^6361 := by
    have hnat : (2128925453 : ℕ)^8409*50000000000000^6361 ≤ 6468799414149^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128925453 10000000000 6468799414149 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542198541/1000000000 : ℝ)^8409 ≤ (44521259845587/100000000000000 : ℝ)^6361 := by
    have hnat : (542198541 : ℕ)^8409*100000000000000^6361 ≤ 44521259845587^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542198541 1000000000 44521259845587 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209542507/400000000 : ℝ)^8409 ≤ (21270570652011/50000000000000 : ℝ)^6361 := by
    have hnat : (209542507 : ℕ)^8409*50000000000000^6361 ≤ 21270570652011^6361*400000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209542507 400000000 21270570652011 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128925453/10000000000 : ℝ), (542198541/1000000000 : ℝ), (209542507/400000000 : ℝ)] ![(6468799414149/50000000000000 : ℝ), (44521259845587/100000000000000 : ℝ), (21270570652011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128925453/10000000000 : ℝ)|^8409 ≤ (6468799414149/50000000000000 : ℝ)^6361
        have hw : |(-2128925453/10000000000 : ℝ)|=(2128925453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542198541/1000000000 : ℝ)|^8409 ≤ (44521259845587/100000000000000 : ℝ)^6361
        have hw : |(542198541/1000000000 : ℝ)|=(542198541/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209542507/400000000 : ℝ)|^8409 ≤ (21270570652011/50000000000000 : ℝ)^6361
        have hw : |(209542507/400000000 : ℝ)|=(209542507/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s3_1 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352069561/10000000000 : ℝ)*x 0 + (-1111271141/5000000000 : ℝ)*x 1 + (2619281237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352069561/10000000000 : ℝ)^8409 ≤ (43763906431543/100000000000000 : ℝ)^6361 := by
    have hnat : (5352069561 : ℕ)^8409*100000000000000^6361 ≤ 43763906431543^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352069561 10000000000 43763906431543 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111271141/5000000000 : ℝ)^8409 ≤ (6847477202849/50000000000000 : ℝ)^6361 := by
    have hnat : (1111271141 : ℕ)^8409*50000000000000^6361 ≤ 6847477202849^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111271141 5000000000 6847477202849 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619281237/5000000000 : ℝ)^8409 ≤ (21270569573109/50000000000000 : ℝ)^6361 := by
    have hnat : (2619281237 : ℕ)^8409*50000000000000^6361 ≤ 21270569573109^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619281237 5000000000 21270569573109 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352069561/10000000000 : ℝ), (-1111271141/5000000000 : ℝ), (2619281237/5000000000 : ℝ)] ![(43763906431543/100000000000000 : ℝ), (6847477202849/50000000000000 : ℝ), (21270569573109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352069561/10000000000 : ℝ)|^8409 ≤ (43763906431543/100000000000000 : ℝ)^6361
        have hw : |(5352069561/10000000000 : ℝ)|=(5352069561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1111271141/5000000000 : ℝ)|^8409 ≤ (6847477202849/50000000000000 : ℝ)^6361
        have hw : |(-1111271141/5000000000 : ℝ)|=(1111271141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619281237/5000000000 : ℝ)|^8409 ≤ (21270569573109/50000000000000 : ℝ)^6361
        have hw : |(2619281237/5000000000 : ℝ)|=(2619281237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s3_2 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352069659/10000000000 : ℝ)*x 0 + (2619281181/5000000000 : ℝ)*x 1 + (-22225423/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352069659/10000000000 : ℝ)^8409 ≤ (10940976872723/25000000000000 : ℝ)^6361 := by
    have hnat : (5352069659 : ℕ)^8409*25000000000000^6361 ≤ 10940976872723^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352069659 10000000000 10940976872723 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619281181/5000000000 : ℝ)^8409 ≤ (2127056897193/5000000000000 : ℝ)^6361 := by
    have hnat : (2619281181 : ℕ)^8409*5000000000000^6361 ≤ 2127056897193^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619281181 5000000000 2127056897193 5000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22225423/100000000 : ℝ)^8409 ≤ (13694954552321/100000000000000 : ℝ)^6361 := by
    have hnat : (22225423 : ℕ)^8409*100000000000000^6361 ≤ 13694954552321^6361*100000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22225423 100000000 13694954552321 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352069659/10000000000 : ℝ), (2619281181/5000000000 : ℝ), (-22225423/100000000 : ℝ)] ![(10940976872723/25000000000000 : ℝ), (2127056897193/5000000000000 : ℝ), (13694954552321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352069659/10000000000 : ℝ)|^8409 ≤ (10940976872723/25000000000000 : ℝ)^6361
        have hw : |(5352069659/10000000000 : ℝ)|=(5352069659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619281181/5000000000 : ℝ)|^8409 ≤ (2127056897193/5000000000000 : ℝ)^6361
        have hw : |(2619281181/5000000000 : ℝ)|=(2619281181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22225423/100000000 : ℝ)|^8409 ≤ (13694954552321/100000000000000 : ℝ)^6361
        have hw : |(-22225423/100000000 : ℝ)|=(22225423/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s3_3 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2176261189/5000000000 : ℝ)*x 0 + (4171258367/10000000000 : ℝ)*x 1 + (4541477571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176261189/5000000000 : ℝ)^8409 ≤ (16649429888641/50000000000000 : ℝ)^6361 := by
    have hnat : (2176261189 : ℕ)^8409*50000000000000^6361 ≤ 16649429888641^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176261189 5000000000 16649429888641 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171258367/10000000000 : ℝ)^8409 ≤ (31478029694371/100000000000000 : ℝ)^6361 := by
    have hnat : (4171258367 : ℕ)^8409*100000000000000^6361 ≤ 31478029694371^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171258367 10000000000 31478029694371 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4541477571/10000000000 : ℝ)^8409 ≤ (35223110507313/100000000000000 : ℝ)^6361 := by
    have hnat : (4541477571 : ℕ)^8409*100000000000000^6361 ≤ 35223110507313^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4541477571 10000000000 35223110507313 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176261189/5000000000 : ℝ), (4171258367/10000000000 : ℝ), (4541477571/10000000000 : ℝ)] ![(16649429888641/50000000000000 : ℝ), (31478029694371/100000000000000 : ℝ), (35223110507313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176261189/5000000000 : ℝ)|^8409 ≤ (16649429888641/50000000000000 : ℝ)^6361
        have hw : |(2176261189/5000000000 : ℝ)|=(2176261189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171258367/10000000000 : ℝ)|^8409 ≤ (31478029694371/100000000000000 : ℝ)^6361
        have hw : |(4171258367/10000000000 : ℝ)|=(4171258367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4541477571/10000000000 : ℝ)|^8409 ≤ (35223110507313/100000000000000 : ℝ)^6361
        have hw : |(4541477571/10000000000 : ℝ)|=(4541477571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s3_4 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-425788063/2000000000 : ℝ)*x 0 + (654905019/1250000000 : ℝ)*x 1 + (1355326093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425788063/2000000000 : ℝ)^8409 ≤ (12937718224339/100000000000000 : ℝ)^6361 := by
    have hnat : (425788063 : ℕ)^8409*100000000000000^6361 ≤ 12937718224339^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425788063 2000000000 12937718224339 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654905019/1250000000 : ℝ)^8409 ≤ (21274207201909/50000000000000 : ℝ)^6361 := by
    have hnat : (654905019 : ℕ)^8409*50000000000000^6361 ≤ 21274207201909^6361*1250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654905019 1250000000 21274207201909 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355326093/2500000000 : ℝ)^8409 ≤ (8902773471543/20000000000000 : ℝ)^6361 := by
    have hnat : (1355326093 : ℕ)^8409*20000000000000^6361 ≤ 8902773471543^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355326093 2500000000 8902773471543 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-425788063/2000000000 : ℝ), (654905019/1250000000 : ℝ), (1355326093/2500000000 : ℝ)] ![(12937718224339/100000000000000 : ℝ), (21274207201909/50000000000000 : ℝ), (8902773471543/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-425788063/2000000000 : ℝ)|^8409 ≤ (12937718224339/100000000000000 : ℝ)^6361
        have hw : |(-425788063/2000000000 : ℝ)|=(425788063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654905019/1250000000 : ℝ)|^8409 ≤ (21274207201909/50000000000000 : ℝ)^6361
        have hw : |(654905019/1250000000 : ℝ)|=(654905019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355326093/2500000000 : ℝ)|^8409 ≤ (8902773471543/20000000000000 : ℝ)^6361
        have hw : |(1355326093/2500000000 : ℝ)|=(1355326093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s3_5 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652678011/5000000000 : ℝ)*x 0 + (-2039800377/10000000000 : ℝ)*x 1 + (5421304563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652678011/5000000000 : ℝ)^8409 ≤ (10814914600687/25000000000000 : ℝ)^6361 := by
    have hnat : (2652678011 : ℕ)^8409*25000000000000^6361 ≤ 10814914600687^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652678011 5000000000 10814914600687 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2039800377/10000000000 : ℝ)^8409 ≤ (12226472151607/100000000000000 : ℝ)^6361 := by
    have hnat : (2039800377 : ℕ)^8409*100000000000000^6361 ≤ 12226472151607^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039800377 10000000000 12226472151607 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421304563/10000000000 : ℝ)^8409 ≤ (44513869430927/100000000000000 : ℝ)^6361 := by
    have hnat : (5421304563 : ℕ)^8409*100000000000000^6361 ≤ 44513869430927^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421304563 10000000000 44513869430927 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652678011/5000000000 : ℝ), (-2039800377/10000000000 : ℝ), (5421304563/10000000000 : ℝ)] ![(10814914600687/25000000000000 : ℝ), (12226472151607/100000000000000 : ℝ), (44513869430927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652678011/5000000000 : ℝ)|^8409 ≤ (10814914600687/25000000000000 : ℝ)^6361
        have hw : |(2652678011/5000000000 : ℝ)|=(2652678011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2039800377/10000000000 : ℝ)|^8409 ≤ (12226472151607/100000000000000 : ℝ)^6361
        have hw : |(-2039800377/10000000000 : ℝ)|=(2039800377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421304563/10000000000 : ℝ)|^8409 ≤ (44513869430927/100000000000000 : ℝ)^6361
        have hw : |(5421304563/10000000000 : ℝ)|=(5421304563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s3_6 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061071221/2000000000 : ℝ)*x 0 + (271065223/500000000 : ℝ)*x 1 + (-1019900203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061071221/2000000000 : ℝ)^8409 ≤ (43259659297423/100000000000000 : ℝ)^6361 := by
    have hnat : (1061071221 : ℕ)^8409*100000000000000^6361 ≤ 43259659297423^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061071221 2000000000 43259659297423 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271065223/500000000 : ℝ)^8409 ≤ (2782116769557/6250000000000 : ℝ)^6361 := by
    have hnat : (271065223 : ℕ)^8409*6250000000000^6361 ≤ 2782116769557^6361*500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271065223 500000000 2782116769557 6250000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019900203/5000000000 : ℝ)^8409 ≤ (12226472381397/100000000000000 : ℝ)^6361 := by
    have hnat : (1019900203 : ℕ)^8409*100000000000000^6361 ≤ 12226472381397^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019900203 5000000000 12226472381397 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061071221/2000000000 : ℝ), (271065223/500000000 : ℝ), (-1019900203/5000000000 : ℝ)] ![(43259659297423/100000000000000 : ℝ), (2782116769557/6250000000000 : ℝ), (12226472381397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061071221/2000000000 : ℝ)|^8409 ≤ (43259659297423/100000000000000 : ℝ)^6361
        have hw : |(1061071221/2000000000 : ℝ)|=(1061071221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271065223/500000000 : ℝ)|^8409 ≤ (2782116769557/6250000000000 : ℝ)^6361
        have hw : |(271065223/500000000 : ℝ)|=(271065223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1019900203/5000000000 : ℝ)|^8409 ≤ (12226472381397/100000000000000 : ℝ)^6361
        have hw : |(-1019900203/5000000000 : ℝ)|=(1019900203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s3_7 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272034529/625000000 : ℝ)*x 0 + (2270055143/5000000000 : ℝ)*x 1 + (2086316481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272034529/625000000 : ℝ)^8409 ≤ (6659832811293/20000000000000 : ℝ)^6361 := by
    have hnat : (272034529 : ℕ)^8409*20000000000000^6361 ≤ 6659832811293^6361*625000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272034529 625000000 6659832811293 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270055143/5000000000 : ℝ)^8409 ≤ (17604546230549/50000000000000 : ℝ)^6361 := by
    have hnat : (2270055143 : ℕ)^8409*50000000000000^6361 ≤ 17604546230549^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270055143 5000000000 17604546230549 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086316481/5000000000 : ℝ)^8409 ≤ (31491743475173/100000000000000 : ℝ)^6361 := by
    have hnat : (2086316481 : ℕ)^8409*100000000000000^6361 ≤ 31491743475173^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086316481 5000000000 31491743475173 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272034529/625000000 : ℝ), (2270055143/5000000000 : ℝ), (2086316481/5000000000 : ℝ)] ![(6659832811293/20000000000000 : ℝ), (17604546230549/50000000000000 : ℝ), (31491743475173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272034529/625000000 : ℝ)|^8409 ≤ (6659832811293/20000000000000 : ℝ)^6361
        have hw : |(272034529/625000000 : ℝ)|=(272034529/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2270055143/5000000000 : ℝ)|^8409 ≤ (17604546230549/50000000000000 : ℝ)^6361
        have hw : |(2270055143/5000000000 : ℝ)|=(2270055143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086316481/5000000000 : ℝ)|^8409 ≤ (31491743475173/100000000000000 : ℝ)^6361
        have hw : |(2086316481/5000000000 : ℝ)|=(2086316481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1216_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4073/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (587/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (10843/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (589/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4073/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (587/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4073/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (587/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4073/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (587/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4073/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (587/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4073/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (587/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4073/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (587/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (587/6250 : ℝ) ^ (1051/256 : ℝ) ≤ (6063039739473347/100000000000000000000 : ℝ) := by
    have hpowers : (587/6250 : ℝ)^1051 ≤ (6063039739473347/100000000000000000000 : ℝ)^256 := by
      have hnat : (587 : ℕ)^1051*100000000000000000000^256 ≤ 6063039739473347^256*6250^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        587 6250 6063039739473347 100000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (587/6250 : ℝ)) (X := (6063039739473347/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hpowhi : (4073/25000 : ℝ) ^ (1051/256 : ℝ) ≤ (5818158266274629/10000000000000000000 : ℝ) := by
    have hpowers : (4073/25000 : ℝ)^1051 ≤ (5818158266274629/10000000000000000000 : ℝ)^256 := by
      have hnat : (4073 : ℕ)^1051*10000000000000000000^256 ≤ 5818158266274629^256*25000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4073 25000 5818158266274629 10000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4073/25000 : ℝ)) (X := (5818158266274629/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006063039739473347/50000000000000000000 : ℝ) ≤ (200005907010443/200000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (50006063039739473347/50000000000000000000 : ℝ)^256 ≤ (200005907010443/200000000000000 : ℝ)^1051 := by
      have hnat : (50006063039739473347 : ℕ)^256*200000000000000^1051 ≤ 200005907010443^1051*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006063039739473347 50000000000000000000 200005907010443 200000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200005907010443/200000000000000 : ℝ)) (X := (50006063039739473347/50000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100064244622402219637/100000000000000000000 : ℝ) ≤ (2000312894931127/2000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (100064244622402219637/100000000000000000000 : ℝ)^256 ≤ (2000312894931127/2000000000000000 : ℝ)^1051 := by
      have hnat : (100064244622402219637 : ℕ)^256*2000000000000000^1051 ≤ 2000312894931127^1051*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100064244622402219637 100000000000000000000 2000312894931127 2000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000312894931127/2000000000000000 : ℝ)) (X := (100064244622402219637/100000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5005818158266274629/5000000000000000000 : ℝ) ≤ (3907356874527/3906250000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (5005818158266274629/5000000000000000000 : ℝ)^256 ≤ (3907356874527/3906250000000 : ℝ)^1051 := by
      have hnat : (5005818158266274629 : ℕ)^256*3906250000000^1051 ≤ 3907356874527^1051*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5005818158266274629 5000000000000000000 3907356874527 3906250000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3907356874527/3906250000000 : ℝ)) (X := (5005818158266274629/5000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6063039739473347/100000000000000000000 : ℝ) ≤ ((1724454967271986319/1725000000000000000 : ℝ)+2*(253824826697/138000000000000 : ℝ)*(587/6250 : ℝ))^(1051/256 : ℝ) := by
    rw [show (1724454967271986319/1725000000000000000 : ℝ)+2*(253824826697/138000000000000 : ℝ)*(587/6250 : ℝ)=(200005907010443/200000000000000 : ℝ) by norm_num, show 1+2*(6063039739473347/100000000000000000000 : ℝ)=(50006063039739473347/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5818158266274629/10000000000000000000 : ℝ)+(6063039739473347/100000000000000000000 : ℝ) ≤ ((1724454967271986319/1725000000000000000 : ℝ)+(253824826697/138000000000000 : ℝ)*((4073/25000 : ℝ)+(587/6250 : ℝ)))^(1051/256 : ℝ) := by
    rw [show (1724454967271986319/1725000000000000000 : ℝ)+(253824826697/138000000000000 : ℝ)*((4073/25000 : ℝ)+(587/6250 : ℝ))=(2000312894931127/2000000000000000 : ℝ) by norm_num, show 1+(5818158266274629/10000000000000000000 : ℝ)+(6063039739473347/100000000000000000000 : ℝ)=(100064244622402219637/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5818158266274629/10000000000000000000 : ℝ) ≤ ((1724454967271986319/1725000000000000000 : ℝ)+2*(253824826697/138000000000000 : ℝ)*(4073/25000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (1724454967271986319/1725000000000000000 : ℝ)+2*(253824826697/138000000000000 : ℝ)*(4073/25000 : ℝ)=(3907356874527/3906250000000 : ℝ) by norm_num, show 1+2*(5818158266274629/10000000000000000000 : ℝ)=(5005818158266274629/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1724454967271986319/1725000000000000000 : ℝ)*(X 1 0+X 2 0)+(253824826697/138000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (587/6250 : ℝ)) (hi := (4073/25000 : ℝ)) (c := (1724454967271986319/1725000000000000000 : ℝ)) (alpha := (253824826697/138000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1724454967271986319/1725000000000000000 : ℝ)*(X 0 1+X 2 1)+(253824826697/138000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (587/6250 : ℝ)) (hi := (4073/25000 : ℝ)) (c := (1724454967271986319/1725000000000000000 : ℝ)) (alpha := (253824826697/138000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1724454967271986319/1725000000000000000 : ℝ)*(X 0 2+X 1 2)+(253824826697/138000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (587/6250 : ℝ)) (hi := (4073/25000 : ℝ)) (c := (1724454967271986319/1725000000000000000 : ℝ)) (alpha := (253824826697/138000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2128925453/10000000000 : ℝ)*X 0 0+(542198541/1000000000 : ℝ)*X 0 1+(209542507/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352069561/10000000000 : ℝ)*X 1 0+(-1111271141/5000000000 : ℝ)*X 1 1+(2619281237/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352069659/10000000000 : ℝ)*X 2 0+(2619281181/5000000000 : ℝ)*X 2 1+(-22225423/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2176261189/5000000000 : ℝ)*X 0 0+(4171258367/10000000000 : ℝ)*X 0 1+(4541477571/10000000000 : ℝ)*X 0 2+(2176261189/5000000000 : ℝ)*X 1 0+(4171258367/10000000000 : ℝ)*X 1 1+(4541477571/10000000000 : ℝ)*X 1 2+(2176261189/5000000000 : ℝ)*X 2 0+(4171258367/10000000000 : ℝ)*X 2 1+(4541477571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-425788063/2000000000 : ℝ)*X 0 0+(654905019/1250000000 : ℝ)*X 0 1+(1355326093/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652678011/5000000000 : ℝ)*X 1 0+(-2039800377/10000000000 : ℝ)*X 1 1+(5421304563/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061071221/2000000000 : ℝ)*X 2 0+(271065223/500000000 : ℝ)*X 2 1+(-1019900203/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272034529/625000000 : ℝ)*X 0 0+(2270055143/5000000000 : ℝ)*X 0 1+(2086316481/5000000000 : ℝ)*X 0 2+(272034529/625000000 : ℝ)*X 1 0+(2270055143/5000000000 : ℝ)*X 1 1+(2086316481/5000000000 : ℝ)*X 1 2+(272034529/625000000 : ℝ)*X 2 0+(2270055143/5000000000 : ℝ)*X 2 1+(2086316481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26314092013111395089745081/3593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1667581569/100000000000000 : ℝ)*(base19) + (1686788959/100000000000000 : ℝ)*(base23) + (5393633/12500000000000 : ℝ)*(lower2) + (51601981/25000000000000 : ℝ)*(upper3) + (28520981/20000000000000 : ℝ)*(upper5) + (509566939379349/12500000000000 : ℝ)*(major0) + (509566939379349/12500000000000 : ℝ)*(major1) + (509566939379349/12500000000000 : ℝ)*(major2) + (2725956739530699/50000000000000 : ℝ)*(sp0) + (1362984492382321/25000000000000 : ℝ)*(sp1) + (2725968975160947/50000000000000 : ℝ)*(sp2) + (1350557978890967/50000000000000 : ℝ)*(sp3) + (5231609891/20000000000000 : ℝ)*(sp4) + (15191104053/100000000000000 : ℝ)*(sp7) + (2701131148885987/100000000000000 : ℝ)*(f.failure) + (5451939637110853/100000000000000 : ℝ)*(f.sum) + (1732552610873/575000000000000000000000000 : ℝ)*base66 + (56227180452153723/7187500000000000000000000000000 : ℝ)*base68 + (10278879709721277/7187500000000000000000000000000 : ℝ)*base69 + (471792925903723/7187500000000000000000000000000 : ℝ)*base72 + (255031417049/287500000000000000000000000 : ℝ)*base74 + (30162679427153723/7187500000000000000000000000000 : ℝ)*base76 + (58707998978471277/7187500000000000000000000000000 : ℝ)*base77 + (31825857209653723/7187500000000000000000000000000 : ℝ)*base80 + (975258089499/287500000000000000000000000 : ℝ)*base82 + (6293441/1000000000000000000000 : ℝ)*base90 + (6293441/1000000000000000000000 : ℝ)*base92 + (6293441/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7315451584532722251044809/1796875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53841859/12500000000000 : ℝ)*(base19) + (127180121/20000000000000 : ℝ)*(base23) + (69872027/50000000000000 : ℝ)*(upper3) + (8827007/20000000000000 : ℝ)*(lower4) + (15823241/50000000000000 : ℝ)*(upper5) + (64170481370153/1562500000000 : ℝ)*(major0) + (64170481370153/1562500000000 : ℝ)*(major1) + (64170481370153/1562500000000 : ℝ)*(major2) + (1110747731/12500000000000 : ℝ)*(sp1) + (2595991077/20000000000000 : ℝ)*(sp2) + (2746281761205589/50000000000000 : ℝ)*(sp4) + (2746277102847229/50000000000000 : ℝ)*(sp5) + (1373137476638797/25000000000000 : ℝ)*(sp6) + (2721257957261469/100000000000000 : ℝ)*(sp7) + (2721257957261469/100000000000000 : ℝ)*(f.failure) + (2746281761205589/50000000000000 : ℝ)*(f.sum) + (332686626203/862500000000000000000000000 : ℝ)*base65 + (1245506320405107/112304687500000000000000000000 : ℝ)*base68 + (5799523537323553/449218750000000000000000000000 : ℝ)*base70 + (14148141590193981/898437500000000000000000000000 : ℝ)*base72 + (1105910367889/431250000000000000000000000 : ℝ)*base73 + (11638680378162731/898437500000000000000000000000 : ℝ)*base76 + (27731582240778587/1796875000000000000000000000000 : ℝ)*base78 + (8714808073475231/898437500000000000000000000000 : ℝ)*base80 + (1604040567247/862500000000000000000000000 : ℝ)*base82 + (7904833/1000000000000000000000 : ℝ)*base89 + (7904833/1000000000000000000000 : ℝ)*base91 + (7904833/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1216_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4073/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (587/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10843/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (589/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1216_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1216_s4_0 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-213138521/1000000000 : ℝ)*x 0 + (215942593/400000000 : ℝ)*x 1 + (2630186029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213138521/1000000000 : ℝ)^8409 ≤ (2591472659333/20000000000000 : ℝ)^6361 := by
    have hnat : (213138521 : ℕ)^8409*20000000000000^6361 ≤ 2591472659333^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213138521 1000000000 2591472659333 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215942593/400000000 : ℝ)^8409 ≤ (22133603693617/50000000000000 : ℝ)^6361 := by
    have hnat : (215942593 : ℕ)^8409*50000000000000^6361 ≤ 22133603693617^6361*400000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215942593 400000000 22133603693617 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630186029/5000000000 : ℝ)^8409 ≤ (8555085858473/20000000000000 : ℝ)^6361 := by
    have hnat : (2630186029 : ℕ)^8409*20000000000000^6361 ≤ 8555085858473^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630186029 5000000000 8555085858473 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213138521/1000000000 : ℝ), (215942593/400000000 : ℝ), (2630186029/5000000000 : ℝ)] ![(2591472659333/20000000000000 : ℝ), (22133603693617/50000000000000 : ℝ), (8555085858473/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213138521/1000000000 : ℝ)|^8409 ≤ (2591472659333/20000000000000 : ℝ)^6361
        have hw : |(-213138521/1000000000 : ℝ)|=(213138521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215942593/400000000 : ℝ)|^8409 ≤ (22133603693617/50000000000000 : ℝ)^6361
        have hw : |(215942593/400000000 : ℝ)|=(215942593/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630186029/5000000000 : ℝ)|^8409 ≤ (8555085858473/20000000000000 : ℝ)^6361
        have hw : |(2630186029/5000000000 : ℝ)|=(2630186029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s4_1 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346178911/10000000000 : ℝ)*x 0 + (-220156367/1000000000 : ℝ)*x 1 + (1315093023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346178911/10000000000 : ℝ)^8409 ≤ (21850120804471/50000000000000 : ℝ)^6361 := by
    have hnat : (5346178911 : ℕ)^8409*50000000000000^6361 ≤ 21850120804471^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346178911 10000000000 21850120804471 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220156367/1000000000 : ℝ)^8409 ≤ (540973148359/4000000000000 : ℝ)^6361 := by
    have hnat : (220156367 : ℕ)^8409*4000000000000^6361 ≤ 540973148359^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220156367 1000000000 540973148359 4000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315093023/2500000000 : ℝ)^8409 ≤ (8555085931571/20000000000000 : ℝ)^6361 := by
    have hnat : (1315093023 : ℕ)^8409*20000000000000^6361 ≤ 8555085931571^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315093023 2500000000 8555085931571 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346178911/10000000000 : ℝ), (-220156367/1000000000 : ℝ), (1315093023/2500000000 : ℝ)] ![(21850120804471/50000000000000 : ℝ), (540973148359/4000000000000 : ℝ), (8555085931571/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346178911/10000000000 : ℝ)|^8409 ≤ (21850120804471/50000000000000 : ℝ)^6361
        have hw : |(5346178911/10000000000 : ℝ)|=(5346178911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-220156367/1000000000 : ℝ)|^8409 ≤ (540973148359/4000000000000 : ℝ)^6361
        have hw : |(-220156367/1000000000 : ℝ)|=(220156367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315093023/2500000000 : ℝ)|^8409 ≤ (8555085931571/20000000000000 : ℝ)^6361
        have hw : |(1315093023/2500000000 : ℝ)|=(1315093023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s4_2 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346178949/10000000000 : ℝ)*x 0 + (2630186037/5000000000 : ℝ)*x 1 + (-440312729/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346178949/10000000000 : ℝ)^8409 ≤ (8740048403913/20000000000000 : ℝ)^6361 := by
    have hnat : (5346178949 : ℕ)^8409*20000000000000^6361 ≤ 8740048403913^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346178949 10000000000 8740048403913 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630186037/5000000000 : ℝ)^8409 ≤ (1069385736609/2500000000000 : ℝ)^6361 := by
    have hnat : (2630186037 : ℕ)^8409*2500000000000^6361 ≤ 1069385736609^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630186037 5000000000 1069385736609 2500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440312729/2000000000 : ℝ)^8409 ≤ (13524328505953/100000000000000 : ℝ)^6361 := by
    have hnat : (440312729 : ℕ)^8409*100000000000000^6361 ≤ 13524328505953^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440312729 2000000000 13524328505953 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346178949/10000000000 : ℝ), (2630186037/5000000000 : ℝ), (-440312729/2000000000 : ℝ)] ![(8740048403913/20000000000000 : ℝ), (1069385736609/2500000000000 : ℝ), (13524328505953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346178949/10000000000 : ℝ)|^8409 ≤ (8740048403913/20000000000000 : ℝ)^6361
        have hw : |(5346178949/10000000000 : ℝ)|=(5346178949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630186037/5000000000 : ℝ)|^8409 ≤ (1069385736609/2500000000000 : ℝ)^6361
        have hw : |(2630186037/5000000000 : ℝ)|=(2630186037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-440312729/2000000000 : ℝ)|^8409 ≤ (13524328505953/100000000000000 : ℝ)^6361
        have hw : |(-440312729/2000000000 : ℝ)|=(440312729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s4_3 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353995223/10000000000 : ℝ)*x 0 + (210835789/500000000 : ℝ)*x 1 + (899128571/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353995223/10000000000 : ℝ)^8409 ≤ (33313756406459/100000000000000 : ℝ)^6361 := by
    have hnat : (4353995223 : ℕ)^8409*100000000000000^6361 ≤ 33313756406459^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353995223 10000000000 33313756406459 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210835789/500000000 : ℝ)^8409 ≤ (3991538694933/12500000000000 : ℝ)^6361 := by
    have hnat : (210835789 : ℕ)^8409*12500000000000^6361 ≤ 3991538694933^6361*500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210835789 500000000 3991538694933 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899128571/2000000000 : ℝ)^8409 ≤ (139015736059/400000000000 : ℝ)^6361 := by
    have hnat : (899128571 : ℕ)^8409*400000000000^6361 ≤ 139015736059^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899128571 2000000000 139015736059 400000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353995223/10000000000 : ℝ), (210835789/500000000 : ℝ), (899128571/2000000000 : ℝ)] ![(33313756406459/100000000000000 : ℝ), (3991538694933/12500000000000 : ℝ), (139015736059/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353995223/10000000000 : ℝ)|^8409 ≤ (33313756406459/100000000000000 : ℝ)^6361
        have hw : |(4353995223/10000000000 : ℝ)|=(4353995223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210835789/500000000 : ℝ)|^8409 ≤ (3991538694933/12500000000000 : ℝ)^6361
        have hw : |(210835789/500000000 : ℝ)|=(210835789/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899128571/2000000000 : ℝ)|^8409 ≤ (139015736059/400000000000 : ℝ)^6361
        have hw : |(899128571/2000000000 : ℝ)|=(899128571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s4_4 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065695843/5000000000 : ℝ)*x 0 + (5260757323/10000000000 : ℝ)*x 1 + (2699088977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065695843/5000000000 : ℝ)^8409 ≤ (6478707670933/50000000000000 : ℝ)^6361 := by
    have hnat : (1065695843 : ℕ)^8409*50000000000000^6361 ≤ 6478707670933^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065695843 5000000000 6478707670933 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260757323/10000000000 : ℝ)^8409 ≤ (42779570829391/100000000000000 : ℝ)^6361 := by
    have hnat : (5260757323 : ℕ)^8409*100000000000000^6361 ≤ 42779570829391^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260757323 10000000000 42779570829391 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699088977/5000000000 : ℝ)^8409 ≤ (44263013816939/100000000000000 : ℝ)^6361 := by
    have hnat : (2699088977 : ℕ)^8409*100000000000000^6361 ≤ 44263013816939^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699088977 5000000000 44263013816939 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065695843/5000000000 : ℝ), (5260757323/10000000000 : ℝ), (2699088977/5000000000 : ℝ)] ![(6478707670933/50000000000000 : ℝ), (42779570829391/100000000000000 : ℝ), (44263013816939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065695843/5000000000 : ℝ)|^8409 ≤ (6478707670933/50000000000000 : ℝ)^6361
        have hw : |(-1065695843/5000000000 : ℝ)|=(1065695843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260757323/10000000000 : ℝ)|^8409 ≤ (42779570829391/100000000000000 : ℝ)^6361
        have hw : |(5260757323/10000000000 : ℝ)|=(5260757323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699088977/5000000000 : ℝ)|^8409 ≤ (44263013816939/100000000000000 : ℝ)^6361
        have hw : |(2699088977/5000000000 : ℝ)|=(2699088977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s4_5 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310982931/10000000000 : ℝ)*x 0 + (-2063757769/10000000000 : ℝ)*x 1 + (1349544499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310982931/10000000000 : ℝ)^8409 ≤ (5415040308807/12500000000000 : ℝ)^6361 := by
    have hnat : (5310982931 : ℕ)^8409*12500000000000^6361 ≤ 5415040308807^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310982931 10000000000 5415040308807 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063757769/10000000000 : ℝ)^8409 ≤ (12416663246579/100000000000000 : ℝ)^6361 := by
    have hnat : (2063757769 : ℕ)^8409*100000000000000^6361 ≤ 12416663246579^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063757769 10000000000 12416663246579 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349544499/2500000000 : ℝ)^8409 ≤ (22131507136101/50000000000000 : ℝ)^6361 := by
    have hnat : (1349544499 : ℕ)^8409*50000000000000^6361 ≤ 22131507136101^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349544499 2500000000 22131507136101 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310982931/10000000000 : ℝ), (-2063757769/10000000000 : ℝ), (1349544499/2500000000 : ℝ)] ![(5415040308807/12500000000000 : ℝ), (12416663246579/100000000000000 : ℝ), (22131507136101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310982931/10000000000 : ℝ)|^8409 ≤ (5415040308807/12500000000000 : ℝ)^6361
        have hw : |(5310982931/10000000000 : ℝ)|=(5310982931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2063757769/10000000000 : ℝ)|^8409 ≤ (12416663246579/100000000000000 : ℝ)^6361
        have hw : |(-2063757769/10000000000 : ℝ)|=(2063757769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349544499/2500000000 : ℝ)|^8409 ≤ (22131507136101/50000000000000 : ℝ)^6361
        have hw : |(1349544499/2500000000 : ℝ)|=(1349544499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s4_6 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655491429/5000000000 : ℝ)*x 0 + (5398178063/10000000000 : ℝ)*x 1 + (-128984861/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655491429/5000000000 : ℝ)^8409 ≤ (5415040210413/12500000000000 : ℝ)^6361 := by
    have hnat : (2655491429 : ℕ)^8409*12500000000000^6361 ≤ 5415040210413^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655491429 5000000000 5415040210413 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398178063/10000000000 : ℝ)^8409 ≤ (22131507499227/50000000000000 : ℝ)^6361 := by
    have hnat : (5398178063 : ℕ)^8409*50000000000000^6361 ≤ 22131507499227^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398178063 10000000000 22131507499227 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128984861/625000000 : ℝ)^8409 ≤ (2483332660451/20000000000000 : ℝ)^6361 := by
    have hnat : (128984861 : ℕ)^8409*20000000000000^6361 ≤ 2483332660451^6361*625000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128984861 625000000 2483332660451 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655491429/5000000000 : ℝ), (5398178063/10000000000 : ℝ), (-128984861/625000000 : ℝ)] ![(5415040210413/12500000000000 : ℝ), (22131507499227/50000000000000 : ℝ), (2483332660451/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655491429/5000000000 : ℝ)|^8409 ≤ (5415040210413/12500000000000 : ℝ)^6361
        have hw : |(2655491429/5000000000 : ℝ)|=(2655491429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398178063/10000000000 : ℝ)|^8409 ≤ (22131507499227/50000000000000 : ℝ)^6361
        have hw : |(5398178063/10000000000 : ℝ)|=(5398178063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-128984861/625000000 : ℝ)|^8409 ≤ (2483332660451/20000000000000 : ℝ)^6361
        have hw : |(-128984861/625000000 : ℝ)|=(128984861/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s4_7 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (544251013/1250000000 : ℝ)*x 0 + (2247432659/5000000000 : ℝ)*x 1 + (2108748229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544251013/1250000000 : ℝ)^8409 ≤ (16656943347227/50000000000000 : ℝ)^6361 := by
    have hnat : (544251013 : ℕ)^8409*50000000000000^6361 ≤ 16656943347227^6361*1250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544251013 1250000000 16656943347227 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247432659/5000000000 : ℝ)^8409 ≤ (3474598816957/10000000000000 : ℝ)^6361 := by
    have hnat : (2247432659 : ℕ)^8409*10000000000000^6361 ≤ 3474598816957^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247432659 5000000000 3474598816957 10000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108748229/5000000000 : ℝ)^8409 ≤ (15970062557399/50000000000000 : ℝ)^6361 := by
    have hnat : (2108748229 : ℕ)^8409*50000000000000^6361 ≤ 15970062557399^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108748229 5000000000 15970062557399 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544251013/1250000000 : ℝ), (2247432659/5000000000 : ℝ), (2108748229/5000000000 : ℝ)] ![(16656943347227/50000000000000 : ℝ), (3474598816957/10000000000000 : ℝ), (15970062557399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544251013/1250000000 : ℝ)|^8409 ≤ (16656943347227/50000000000000 : ℝ)^6361
        have hw : |(544251013/1250000000 : ℝ)|=(544251013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247432659/5000000000 : ℝ)|^8409 ≤ (3474598816957/10000000000000 : ℝ)^6361
        have hw : |(2247432659/5000000000 : ℝ)|=(2247432659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2108748229/5000000000 : ℝ)|^8409 ≤ (15970062557399/50000000000000 : ℝ)^6361
        have hw : |(2108748229/5000000000 : ℝ)|=(2108748229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1216_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2827/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10843/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10843/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10843/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10843/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10843/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10843/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10843/100000 : ℝ) ^ (1051/256 : ℝ) ≤ (10935439708051217/100000000000000000000 : ℝ) := by
    have hpowers : (10843/100000 : ℝ)^1051 ≤ (10935439708051217/100000000000000000000 : ℝ)^256 := by
      have hnat : (10843 : ℕ)^1051*100000000000000000000^256 ≤ 10935439708051217^256*100000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10843 100000 10935439708051217 100000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10843/100000 : ℝ)) (X := (10935439708051217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hpowhi : (589/4000 : ℝ) ^ (1051/256 : ℝ) ≤ (19206447830951263/50000000000000000000 : ℝ) := by
    have hpowers : (589/4000 : ℝ)^1051 ≤ (19206447830951263/50000000000000000000 : ℝ)^256 := by
      have hnat : (589 : ℕ)^1051*50000000000000000000^256 ≤ 19206447830951263^256*4000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        589 4000 19206447830951263 50000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (589/4000 : ℝ)) (X := (19206447830951263/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010935439708051217/50000000000000000000 : ℝ) ≤ (2500133170362883/2500000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (50010935439708051217/50000000000000000000 : ℝ)^256 ≤ (2500133170362883/2500000000000000 : ℝ)^1051 := by
      have hnat : (50010935439708051217 : ℕ)^256*2500000000000000^1051 ≤ 2500133170362883^1051*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010935439708051217 50000000000000000000 2500133170362883 2500000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500133170362883/2500000000000000 : ℝ)) (X := (50010935439708051217/50000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049348335369953743/100000000000000000000 : ℝ) ≤ (1250150223794817/1250000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (100049348335369953743/100000000000000000000 : ℝ)^256 ≤ (1250150223794817/1250000000000000 : ℝ)^1051 := by
      have hnat : (100049348335369953743 : ℕ)^256*1250000000000000^1051 ≤ 1250150223794817^1051*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049348335369953743 100000000000000000000 1250150223794817 1250000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250150223794817/1250000000000000 : ℝ)) (X := (100049348335369953743/100000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019206447830951263/25000000000000000000 : ℝ) ≤ (500093544963277/500000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (25019206447830951263/25000000000000000000 : ℝ)^256 ≤ (500093544963277/500000000000000 : ℝ)^1051 := by
      have hnat : (25019206447830951263 : ℕ)^256*500000000000000^1051 ≤ 500093544963277^1051*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019206447830951263 25000000000000000000 500093544963277 500000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500093544963277/500000000000000 : ℝ)) (X := (25019206447830951263/25000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10935439708051217/100000000000000000000 : ℝ) ≤ ((485094469670469481/485250000000000000 : ℝ)+2*(167277226751/97050000000000 : ℝ)*(10843/100000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (485094469670469481/485250000000000000 : ℝ)+2*(167277226751/97050000000000 : ℝ)*(10843/100000 : ℝ)=(2500133170362883/2500000000000000 : ℝ) by norm_num, show 1+2*(10935439708051217/100000000000000000000 : ℝ)=(50010935439708051217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19206447830951263/50000000000000000000 : ℝ)+(10935439708051217/100000000000000000000 : ℝ) ≤ ((485094469670469481/485250000000000000 : ℝ)+(167277226751/97050000000000 : ℝ)*((589/4000 : ℝ)+(10843/100000 : ℝ)))^(1051/256 : ℝ) := by
    rw [show (485094469670469481/485250000000000000 : ℝ)+(167277226751/97050000000000 : ℝ)*((589/4000 : ℝ)+(10843/100000 : ℝ))=(1250150223794817/1250000000000000 : ℝ) by norm_num, show 1+(19206447830951263/50000000000000000000 : ℝ)+(10935439708051217/100000000000000000000 : ℝ)=(100049348335369953743/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19206447830951263/50000000000000000000 : ℝ) ≤ ((485094469670469481/485250000000000000 : ℝ)+2*(167277226751/97050000000000 : ℝ)*(589/4000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (485094469670469481/485250000000000000 : ℝ)+2*(167277226751/97050000000000 : ℝ)*(589/4000 : ℝ)=(500093544963277/500000000000000 : ℝ) by norm_num, show 1+2*(19206447830951263/50000000000000000000 : ℝ)=(25019206447830951263/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (485094469670469481/485250000000000000 : ℝ)*(X 1 0+X 2 0)+(167277226751/97050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (10843/100000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (485094469670469481/485250000000000000 : ℝ)) (alpha := (167277226751/97050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (485094469670469481/485250000000000000 : ℝ)*(X 0 1+X 2 1)+(167277226751/97050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (10843/100000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (485094469670469481/485250000000000000 : ℝ)) (alpha := (167277226751/97050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (485094469670469481/485250000000000000 : ℝ)*(X 0 2+X 1 2)+(167277226751/97050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (10843/100000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (485094469670469481/485250000000000000 : ℝ)) (alpha := (167277226751/97050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-213138521/1000000000 : ℝ)*X 0 0+(215942593/400000000 : ℝ)*X 0 1+(2630186029/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346178911/10000000000 : ℝ)*X 1 0+(-220156367/1000000000 : ℝ)*X 1 1+(1315093023/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346178949/10000000000 : ℝ)*X 2 0+(2630186037/5000000000 : ℝ)*X 2 1+(-440312729/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353995223/10000000000 : ℝ)*X 0 0+(210835789/500000000 : ℝ)*X 0 1+(899128571/2000000000 : ℝ)*X 0 2+(4353995223/10000000000 : ℝ)*X 1 0+(210835789/500000000 : ℝ)*X 1 1+(899128571/2000000000 : ℝ)*X 1 2+(4353995223/10000000000 : ℝ)*X 2 0+(210835789/500000000 : ℝ)*X 2 1+(899128571/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1065695843/5000000000 : ℝ)*X 0 0+(5260757323/10000000000 : ℝ)*X 0 1+(2699088977/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310982931/10000000000 : ℝ)*X 1 0+(-2063757769/10000000000 : ℝ)*X 1 1+(1349544499/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655491429/5000000000 : ℝ)*X 2 0+(5398178063/10000000000 : ℝ)*X 2 1+(-128984861/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((544251013/1250000000 : ℝ)*X 0 0+(2247432659/5000000000 : ℝ)*X 0 1+(2108748229/5000000000 : ℝ)*X 0 2+(544251013/1250000000 : ℝ)*X 1 0+(2247432659/5000000000 : ℝ)*X 1 1+(2108748229/5000000000 : ℝ)*X 1 2+(544251013/1250000000 : ℝ)*X 2 0+(2247432659/5000000000 : ℝ)*X 2 1+(2108748229/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16573432490780125907613/1617500000000000000000000000 : ℝ) := by norm_num
    linear_combination (414065557/20000000000000 : ℝ)*(base19) + (483571113/25000000000000 : ℝ)*(base23) + (100229433/100000000000000 : ℝ)*(lower2) + (123618727/50000000000000 : ℝ)*(upper3) + (19398241/12500000000000 : ℝ)*(upper5) + (5410800635669049/100000000000000 : ℝ)*(major0) + (5410800635669049/100000000000000 : ℝ)*(major1) + (5410800635669049/100000000000000 : ℝ)*(major2) + (7236324535729801/100000000000000 : ℝ)*(sp0) + (1447275503125551/20000000000000 : ℝ)*(sp1) + (7236377651671089/100000000000000 : ℝ)*(sp2) + (3585192394173197/100000000000000 : ℝ)*(sp3) + (2752511287/5000000000000 : ℝ)*(sp4) + (14474832573/50000000000000 : ℝ)*(sp7) + (3585221343838343/100000000000000 : ℝ)*(f.failure) + (7236379585955541/100000000000000 : ℝ)*(f.sum) + (14313463262591/3235000000000000000000000000 : ℝ)*base65 + (78169327401345477/16175000000000000000000000000000 : ℝ)*base68 + (211255644627754523/16175000000000000000000000000000 : ℝ)*base69 + (344634545833929523/16175000000000000000000000000000 : ℝ)*base71 + (113255814999/50546875000000000000000000 : ℝ)*base73 + (210151259026595477/16175000000000000000000000000000 : ℝ)*base76 + (43184220026870477/16175000000000000000000000000000 : ℝ)*base78 + (211074857412979523/16175000000000000000000000000000 : ℝ)*base79 + (3780140341209/808750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2492749/1000000000000000000000 : ℝ)*base90 + (2492749/1000000000000000000000 : ℝ)*base92 + (2492749/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33743205821252012123243331/8087500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (168962051/20000000000000 : ℝ)*(base19) + (781568247/100000000000000 : ℝ)*(base23) + (5655091/50000000000000 : ℝ)*(upper2) + (141093133/100000000000000 : ℝ)*(upper3) + (65392283/100000000000000 : ℝ)*(upper5) + (5441115786025851/100000000000000 : ℝ)*(major0) + (5441115786025851/100000000000000 : ℝ)*(major1) + (5441115786025851/100000000000000 : ℝ)*(major2) + (20190469137/100000000000000 : ℝ)*(sp1) + (5631730751/25000000000000 : ℝ)*(sp2) + (1819230782831309/25000000000000 : ℝ)*(sp4) + (7276902096045843/100000000000000 : ℝ)*(sp5) + (1455379964566797/20000000000000 : ℝ)*(sp6) + (1802654150825453/50000000000000 : ℝ)*(sp7) + (1802654150825453/50000000000000 : ℝ)*(f.failure) + (1819230782831309/25000000000000 : ℝ)*(f.sum) + (557953287827/1617500000000000000000000000 : ℝ)*base65 + (50054078414552777/16175000000000000000000000000000 : ℝ)*base67 + (55118307113747223/16175000000000000000000000000000 : ℝ)*base70 + (36131764925847223/16175000000000000000000000000000 : ℝ)*base72 + (9380468726749/3235000000000000000000000000 : ℝ)*base73 + (138790742437147223/16175000000000000000000000000000 : ℝ)*base76 + (82249864851897223/16175000000000000000000000000000 : ℝ)*base78 + (22136705775027777/16175000000000000000000000000000 : ℝ)*base79 + (6614634030427/1617500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3818479/500000000000000000000 : ℝ)*base90 + (3818479/500000000000000000000 : ℝ)*base92 + (3818479/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1216_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10843/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1216_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1216_s5_0 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131877611/10000000000 : ℝ)*x 0 + (539303987/1000000000 : ℝ)*x 1 + (105311469/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131877611/10000000000 : ℝ)^8409 ≤ (518452827419/4000000000000 : ℝ)^6361 := by
    have hnat : (2131877611 : ℕ)^8409*4000000000000^6361 ≤ 518452827419^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131877611 10000000000 518452827419 4000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539303987/1000000000 : ℝ)^8409 ≤ (22103663821673/50000000000000 : ℝ)^6361 := by
    have hnat : (539303987 : ℕ)^8409*50000000000000^6361 ≤ 22103663821673^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539303987 1000000000 22103663821673 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105311469/200000000 : ℝ)^8409 ≤ (10707837915481/25000000000000 : ℝ)^6361 := by
    have hnat : (105311469 : ℕ)^8409*25000000000000^6361 ≤ 10707837915481^6361*200000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105311469 200000000 10707837915481 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131877611/10000000000 : ℝ), (539303987/1000000000 : ℝ), (105311469/200000000 : ℝ)] ![(518452827419/4000000000000 : ℝ), (22103663821673/50000000000000 : ℝ), (10707837915481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131877611/10000000000 : ℝ)|^8409 ≤ (518452827419/4000000000000 : ℝ)^6361
        have hw : |(-2131877611/10000000000 : ℝ)|=(2131877611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539303987/1000000000 : ℝ)|^8409 ≤ (22103663821673/50000000000000 : ℝ)^6361
        have hw : |(539303987/1000000000 : ℝ)|=(539303987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105311469/200000000 : ℝ)|^8409 ≤ (10707837915481/25000000000000 : ℝ)^6361
        have hw : |(105311469/200000000 : ℝ)|=(105311469/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s5_1 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344784039/10000000000 : ℝ)*x 0 + (-1098265801/5000000000 : ℝ)*x 1 + (5265573447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344784039/10000000000 : ℝ)^8409 ≤ (873703389031/2000000000000 : ℝ)^6361 := by
    have hnat : (5344784039 : ℕ)^8409*2000000000000^6361 ≤ 873703389031^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344784039 10000000000 873703389031 2000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098265801/5000000000 : ℝ)^8409 ≤ (6741739450711/50000000000000 : ℝ)^6361 := by
    have hnat : (1098265801 : ℕ)^8409*50000000000000^6361 ≤ 6741739450711^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098265801 5000000000 6741739450711 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265573447/10000000000 : ℝ)^8409 ≤ (1338479738427/3125000000000 : ℝ)^6361 := by
    have hnat : (5265573447 : ℕ)^8409*3125000000000^6361 ≤ 1338479738427^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265573447 10000000000 1338479738427 3125000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344784039/10000000000 : ℝ), (-1098265801/5000000000 : ℝ), (5265573447/10000000000 : ℝ)] ![(873703389031/2000000000000 : ℝ), (6741739450711/50000000000000 : ℝ), (1338479738427/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344784039/10000000000 : ℝ)|^8409 ≤ (873703389031/2000000000000 : ℝ)^6361
        have hw : |(5344784039/10000000000 : ℝ)|=(5344784039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1098265801/5000000000 : ℝ)|^8409 ≤ (6741739450711/50000000000000 : ℝ)^6361
        have hw : |(-1098265801/5000000000 : ℝ)|=(1098265801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265573447/10000000000 : ℝ)|^8409 ≤ (1338479738427/3125000000000 : ℝ)^6361
        have hw : |(5265573447/10000000000 : ℝ)|=(5265573447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s5_2 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344784037/10000000000 : ℝ)*x 0 + (2632786721/5000000000 : ℝ)*x 1 + (-2196531611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344784037/10000000000 : ℝ)^8409 ≤ (43685169429941/100000000000000 : ℝ)^6361 := by
    have hnat : (5344784037 : ℕ)^8409*100000000000000^6361 ≤ 43685169429941^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344784037 10000000000 43685169429941 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632786721/5000000000 : ℝ)^8409 ≤ (42831351575899/100000000000000 : ℝ)^6361 := by
    have hnat : (2632786721 : ℕ)^8409*100000000000000^6361 ≤ 42831351575899^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632786721 5000000000 42831351575899 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196531611/10000000000 : ℝ)^8409 ≤ (1685434871807/12500000000000 : ℝ)^6361 := by
    have hnat : (2196531611 : ℕ)^8409*12500000000000^6361 ≤ 1685434871807^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196531611 10000000000 1685434871807 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344784037/10000000000 : ℝ), (2632786721/5000000000 : ℝ), (-2196531611/10000000000 : ℝ)] ![(43685169429941/100000000000000 : ℝ), (42831351575899/100000000000000 : ℝ), (1685434871807/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344784037/10000000000 : ℝ)|^8409 ≤ (43685169429941/100000000000000 : ℝ)^6361
        have hw : |(5344784037/10000000000 : ℝ)|=(5344784037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632786721/5000000000 : ℝ)|^8409 ≤ (42831351575899/100000000000000 : ℝ)^6361
        have hw : |(2632786721/5000000000 : ℝ)|=(2632786721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196531611/10000000000 : ℝ)|^8409 ≤ (1685434871807/12500000000000 : ℝ)^6361
        have hw : |(-2196531611/10000000000 : ℝ)|=(2196531611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s5_3 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4354283819/10000000000 : ℝ)*x 0 + (845500749/2000000000 : ℝ)*x 1 + (1121195217/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354283819/10000000000 : ℝ)^8409 ≤ (33316675510377/100000000000000 : ℝ)^6361 := by
    have hnat : (4354283819 : ℕ)^8409*100000000000000^6361 ≤ 33316675510377^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354283819 10000000000 33316675510377 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845500749/2000000000 : ℝ)^8409 ≤ (8010087926977/25000000000000 : ℝ)^6361 := by
    have hnat : (845500749 : ℕ)^8409*25000000000000^6361 ≤ 8010087926977^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845500749 2000000000 8010087926977 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121195217/2500000000 : ℝ)^8409 ≤ (34642972759283/100000000000000 : ℝ)^6361 := by
    have hnat : (1121195217 : ℕ)^8409*100000000000000^6361 ≤ 34642972759283^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121195217 2500000000 34642972759283 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354283819/10000000000 : ℝ), (845500749/2000000000 : ℝ), (1121195217/2500000000 : ℝ)] ![(33316675510377/100000000000000 : ℝ), (8010087926977/25000000000000 : ℝ), (34642972759283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354283819/10000000000 : ℝ)|^8409 ≤ (33316675510377/100000000000000 : ℝ)^6361
        have hw : |(4354283819/10000000000 : ℝ)|=(4354283819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845500749/2000000000 : ℝ)|^8409 ≤ (8010087926977/25000000000000 : ℝ)^6361
        have hw : |(845500749/2000000000 : ℝ)|=(845500749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121195217/2500000000 : ℝ)|^8409 ≤ (34642972759283/100000000000000 : ℝ)^6361
        have hw : |(1121195217/2500000000 : ℝ)|=(1121195217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s5_4 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131882697/10000000000 : ℝ)*x 0 + (1316475351/2500000000 : ℝ)*x 1 + (5392710653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131882697/10000000000 : ℝ)^8409 ≤ (32403403907/250000000000 : ℝ)^6361 := by
    have hnat : (2131882697 : ℕ)^8409*250000000000^6361 ≤ 32403403907^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131882697 10000000000 32403403907 250000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316475351/2500000000 : ℝ)^8409 ≤ (42834878230621/100000000000000 : ℝ)^6361 := by
    have hnat : (1316475351 : ℕ)^8409*100000000000000^6361 ≤ 42834878230621^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316475351 2500000000 42834878230621 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392710653/10000000000 : ℝ)^8409 ≤ (22101880097993/50000000000000 : ℝ)^6361 := by
    have hnat : (5392710653 : ℕ)^8409*50000000000000^6361 ≤ 22101880097993^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392710653 10000000000 22101880097993 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131882697/10000000000 : ℝ), (1316475351/2500000000 : ℝ), (5392710653/10000000000 : ℝ)] ![(32403403907/250000000000 : ℝ), (42834878230621/100000000000000 : ℝ), (22101880097993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131882697/10000000000 : ℝ)|^8409 ≤ (32403403907/250000000000 : ℝ)^6361
        have hw : |(-2131882697/10000000000 : ℝ)|=(2131882697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316475351/2500000000 : ℝ)|^8409 ≤ (42834878230621/100000000000000 : ℝ)^6361
        have hw : |(1316475351/2500000000 : ℝ)|=(1316475351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392710653/10000000000 : ℝ)|^8409 ≤ (22101880097993/50000000000000 : ℝ)^6361
        have hw : |(5392710653/10000000000 : ℝ)|=(5392710653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s5_5 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312318697/10000000000 : ℝ)*x 0 + (-1034697099/5000000000 : ℝ)*x 1 + (2696355341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312318697/10000000000 : ℝ)^8409 ≤ (21667363244959/50000000000000 : ℝ)^6361 := by
    have hnat : (5312318697 : ℕ)^8409*50000000000000^6361 ≤ 21667363244959^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312318697 10000000000 21667363244959 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034697099/5000000000 : ℝ)^8409 ≤ (12461512989991/100000000000000 : ℝ)^6361 := by
    have hnat : (1034697099 : ℕ)^8409*100000000000000^6361 ≤ 12461512989991^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034697099 5000000000 12461512989991 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696355341/5000000000 : ℝ)^8409 ≤ (5525470063779/12500000000000 : ℝ)^6361 := by
    have hnat : (2696355341 : ℕ)^8409*12500000000000^6361 ≤ 5525470063779^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696355341 5000000000 5525470063779 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312318697/10000000000 : ℝ), (-1034697099/5000000000 : ℝ), (2696355341/5000000000 : ℝ)] ![(21667363244959/50000000000000 : ℝ), (12461512989991/100000000000000 : ℝ), (5525470063779/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312318697/10000000000 : ℝ)|^8409 ≤ (21667363244959/50000000000000 : ℝ)^6361
        have hw : |(5312318697/10000000000 : ℝ)|=(5312318697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1034697099/5000000000 : ℝ)|^8409 ≤ (12461512989991/100000000000000 : ℝ)^6361
        have hw : |(-1034697099/5000000000 : ℝ)|=(1034697099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696355341/5000000000 : ℝ)|^8409 ≤ (5525470063779/12500000000000 : ℝ)^6361
        have hw : |(2696355341/5000000000 : ℝ)|=(2696355341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s5_6 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312318537/10000000000 : ℝ)*x 0 + (1348177713/2500000000 : ℝ)*x 1 + (-2069394183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312318537/10000000000 : ℝ)^8409 ≤ (21667362382257/50000000000000 : ℝ)^6361 := by
    have hnat : (5312318537 : ℕ)^8409*50000000000000^6361 ≤ 21667362382257^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312318537 10000000000 21667362382257 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348177713/2500000000 : ℝ)^8409 ≤ (1105094058809/2500000000000 : ℝ)^6361 := by
    have hnat : (1348177713 : ℕ)^8409*2500000000000^6361 ≤ 1105094058809^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348177713 2500000000 1105094058809 2500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069394183/10000000000 : ℝ)^8409 ≤ (12461512870581/100000000000000 : ℝ)^6361 := by
    have hnat : (2069394183 : ℕ)^8409*100000000000000^6361 ≤ 12461512870581^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069394183 10000000000 12461512870581 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312318537/10000000000 : ℝ), (1348177713/2500000000 : ℝ), (-2069394183/10000000000 : ℝ)] ![(21667362382257/50000000000000 : ℝ), (1105094058809/2500000000000 : ℝ), (12461512870581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312318537/10000000000 : ℝ)|^8409 ≤ (21667362382257/50000000000000 : ℝ)^6361
        have hw : |(5312318537/10000000000 : ℝ)|=(5312318537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348177713/2500000000 : ℝ)|^8409 ≤ (1105094058809/2500000000000 : ℝ)^6361
        have hw : |(1348177713/2500000000 : ℝ)|=(1348177713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2069394183/10000000000 : ℝ)|^8409 ≤ (12461512870581/100000000000000 : ℝ)^6361
        have hw : |(-2069394183/10000000000 : ℝ)|=(2069394183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s5_7 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4354294171/10000000000 : ℝ)*x 0 + (4484118917/10000000000 : ℝ)*x 1 + (1057041981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354294171/10000000000 : ℝ)^8409 ≤ (16658390110207/50000000000000 : ℝ)^6361 := by
    have hnat : (4354294171 : ℕ)^8409*50000000000000^6361 ≤ 16658390110207^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354294171 10000000000 16658390110207 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484118917/10000000000 : ℝ)^8409 ≤ (17318106677641/50000000000000 : ℝ)^6361 := by
    have hnat : (4484118917 : ℕ)^8409*50000000000000^6361 ≤ 17318106677641^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484118917 10000000000 17318106677641 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057041981/2500000000 : ℝ)^8409 ≤ (32047006405949/100000000000000 : ℝ)^6361 := by
    have hnat : (1057041981 : ℕ)^8409*100000000000000^6361 ≤ 32047006405949^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057041981 2500000000 32047006405949 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354294171/10000000000 : ℝ), (4484118917/10000000000 : ℝ), (1057041981/2500000000 : ℝ)] ![(16658390110207/50000000000000 : ℝ), (17318106677641/50000000000000 : ℝ), (32047006405949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354294171/10000000000 : ℝ)|^8409 ≤ (16658390110207/50000000000000 : ℝ)^6361
        have hw : |(4354294171/10000000000 : ℝ)|=(4354294171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484118917/10000000000 : ℝ)|^8409 ≤ (17318106677641/50000000000000 : ℝ)^6361
        have hw : |(4484118917/10000000000 : ℝ)|=(4484118917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1057041981/2500000000 : ℝ)|^8409 ≤ (32047006405949/100000000000000 : ℝ)^6361
        have hw : |(1057041981/2500000000 : ℝ)|=(1057041981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1216_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11419/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14119/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2827/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2827/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2827/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2827/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2827/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2827/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2827/25000 : ℝ) ^ (1051/256 : ℝ) ≤ (12992866700171867/100000000000000000000 : ℝ) := by
    have hpowers : (2827/25000 : ℝ)^1051 ≤ (12992866700171867/100000000000000000000 : ℝ)^256 := by
      have hnat : (2827 : ℕ)^1051*100000000000000000000^256 ≤ 12992866700171867^256*25000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2827 25000 12992866700171867 100000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2827/25000 : ℝ)) (X := (12992866700171867/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (1051/256 : ℝ) ≤ (33429936892515889/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^1051 ≤ (33429936892515889/100000000000000000000 : ℝ)^256 := by
      have hnat : (2847 : ℕ)^1051*100000000000000000000^256 ≤ 33429936892515889^256*20000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 33429936892515889 100000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (33429936892515889/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012992866700171867/50000000000000000000 : ℝ) ≤ (10000632891917299/10000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (50012992866700171867/50000000000000000000 : ℝ)^256 ≤ (10000632891917299/10000000000000000 : ℝ)^1051 := by
      have hnat : (50012992866700171867 : ℕ)^256*10000000000000000^1051 ≤ 10000632891917299^1051*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012992866700171867 50000000000000000000 10000632891917299 10000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000632891917299/10000000000000000 : ℝ)) (X := (50012992866700171867/50000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011605700898171939/25000000000000000000 : ℝ) ≤ (2500282639193547/2500000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (25011605700898171939/25000000000000000000 : ℝ)^256 ≤ (2500282639193547/2500000000000000 : ℝ)^1051 := by
      have hnat : (25011605700898171939 : ℕ)^256*2500000000000000^1051 ≤ 2500282639193547^1051*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011605700898171939 25000000000000000000 2500282639193547 2500000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500282639193547/2500000000000000 : ℝ)) (X := (25011605700898171939/25000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033429936892515889/50000000000000000000 : ℝ) ≤ (10001628221631077/10000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (50033429936892515889/50000000000000000000 : ℝ)^256 ≤ (10001628221631077/10000000000000000 : ℝ)^1051 := by
      have hnat : (50033429936892515889 : ℕ)^256*10000000000000000^1051 ≤ 10001628221631077^1051*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033429936892515889 50000000000000000000 10001628221631077 10000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001628221631077/10000000000000000 : ℝ)) (X := (50033429936892515889/50000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12992866700171867/100000000000000000000 : ℝ) ≤ ((29260597286238532549/29270000000000000000 : ℝ)+2*(497664856889/292700000000000 : ℝ)*(2827/25000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (29260597286238532549/29270000000000000000 : ℝ)+2*(497664856889/292700000000000 : ℝ)*(2827/25000 : ℝ)=(10000632891917299/10000000000000000 : ℝ) by norm_num, show 1+2*(12992866700171867/100000000000000000000 : ℝ)=(50012992866700171867/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33429936892515889/100000000000000000000 : ℝ)+(12992866700171867/100000000000000000000 : ℝ) ≤ ((29260597286238532549/29270000000000000000 : ℝ)+(497664856889/292700000000000 : ℝ)*((2847/20000 : ℝ)+(2827/25000 : ℝ)))^(1051/256 : ℝ) := by
    rw [show (29260597286238532549/29270000000000000000 : ℝ)+(497664856889/292700000000000 : ℝ)*((2847/20000 : ℝ)+(2827/25000 : ℝ))=(2500282639193547/2500000000000000 : ℝ) by norm_num, show 1+(33429936892515889/100000000000000000000 : ℝ)+(12992866700171867/100000000000000000000 : ℝ)=(25011605700898171939/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33429936892515889/100000000000000000000 : ℝ) ≤ ((29260597286238532549/29270000000000000000 : ℝ)+2*(497664856889/292700000000000 : ℝ)*(2847/20000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (29260597286238532549/29270000000000000000 : ℝ)+2*(497664856889/292700000000000 : ℝ)*(2847/20000 : ℝ)=(10001628221631077/10000000000000000 : ℝ) by norm_num, show 1+2*(33429936892515889/100000000000000000000 : ℝ)=(50033429936892515889/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29260597286238532549/29270000000000000000 : ℝ)*(X 1 0+X 2 0)+(497664856889/292700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (2827/25000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (29260597286238532549/29270000000000000000 : ℝ)) (alpha := (497664856889/292700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29260597286238532549/29270000000000000000 : ℝ)*(X 0 1+X 2 1)+(497664856889/292700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (2827/25000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (29260597286238532549/29270000000000000000 : ℝ)) (alpha := (497664856889/292700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29260597286238532549/29270000000000000000 : ℝ)*(X 0 2+X 1 2)+(497664856889/292700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (2827/25000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (29260597286238532549/29270000000000000000 : ℝ)) (alpha := (497664856889/292700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2131877611/10000000000 : ℝ)*X 0 0+(539303987/1000000000 : ℝ)*X 0 1+(105311469/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344784039/10000000000 : ℝ)*X 1 0+(-1098265801/5000000000 : ℝ)*X 1 1+(5265573447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344784037/10000000000 : ℝ)*X 2 0+(2632786721/5000000000 : ℝ)*X 2 1+(-2196531611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354283819/10000000000 : ℝ)*X 0 0+(845500749/2000000000 : ℝ)*X 0 1+(1121195217/2500000000 : ℝ)*X 0 2+(4354283819/10000000000 : ℝ)*X 1 0+(845500749/2000000000 : ℝ)*X 1 1+(1121195217/2500000000 : ℝ)*X 1 2+(4354283819/10000000000 : ℝ)*X 2 0+(845500749/2000000000 : ℝ)*X 2 1+(1121195217/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2131882697/10000000000 : ℝ)*X 0 0+(1316475351/2500000000 : ℝ)*X 0 1+(5392710653/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312318697/10000000000 : ℝ)*X 1 0+(-1034697099/5000000000 : ℝ)*X 1 1+(2696355341/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312318537/10000000000 : ℝ)*X 2 0+(1348177713/2500000000 : ℝ)*X 2 1+(-2069394183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354294171/10000000000 : ℝ)*X 0 0+(4484118917/10000000000 : ℝ)*X 0 1+(1057041981/2500000000 : ℝ)*X 0 2+(4354294171/10000000000 : ℝ)*X 1 0+(4484118917/10000000000 : ℝ)*X 1 1+(1057041981/2500000000 : ℝ)*X 1 2+(4354294171/10000000000 : ℝ)*X 2 0+(4484118917/10000000000 : ℝ)*X 2 1+(1057041981/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1308646630907218147313554209/146350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (348501373/20000000000000 : ℝ)*(base19) + (201686009/12500000000000 : ℝ)*(base23) + (33694349/50000000000000 : ℝ)*(lower2) + (11733133/5000000000000 : ℝ)*(upper3) + (63238467/50000000000000 : ℝ)*(upper5) + (586610313948447/10000000000000 : ℝ)*(major0) + (586610313948447/10000000000000 : ℝ)*(major1) + (586610313948447/10000000000000 : ℝ)*(major2) + (7845252861439289/100000000000000 : ℝ)*(sp0) + (7845297365099057/100000000000000 : ℝ)*(sp1) + (156905949882357/2000000000000 : ℝ)*(sp2) + (3886881649453261/100000000000000 : ℝ)*(sp3) + (23123083317/50000000000000 : ℝ)*(sp4) + (25223846517/100000000000000 : ℝ)*(sp7) + (1943453436649889/50000000000000 : ℝ)*(f.failure) + (3922649553802961/50000000000000 : ℝ)*(f.sum) + (6699453671063/2927000000000000000000000000 : ℝ)*base65 + (401728587514198597/292700000000000000000000000000000 : ℝ)*base68 + (1935514406695798597/292700000000000000000000000000000 : ℝ)*base70 + (1695245546695501403/292700000000000000000000000000000 : ℝ)*base71 + (4290737658087/1463500000000000000000000000 : ℝ)*base74 + (249868551321301403/292700000000000000000000000000000 : ℝ)*base75 + (1398361994047398597/292700000000000000000000000000000 : ℝ)*base78 + (1402216155835998597/292700000000000000000000000000000 : ℝ)*base80 + (1604112081613/365875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1157227/500000000000000000000 : ℝ)*base90 + (1157227/500000000000000000000 : ℝ)*base92 + (1157227/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (971446481424545786641986759/731750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (908920853/100000000000000 : ℝ)*(base19) + (99448923/12500000000000 : ℝ)*(base23) + (145787923/100000000000000 : ℝ)*(upper3) + (23538509/50000000000000 : ℝ)*(lower4) + (48933367/100000000000000 : ℝ)*(upper5) + (5896425140104903/100000000000000 : ℝ)*(major0) + (5896425140104903/100000000000000 : ℝ)*(major1) + (5896425140104903/100000000000000 : ℝ)*(major2) + (727184637/3125000000000 : ℝ)*(sp1) + (29089010389/100000000000000 : ℝ)*(sp2) + (7885851865829123/100000000000000 : ℝ)*(sp4) + (3942913843499943/50000000000000 : ℝ)*(sp5) + (7885821981227349/100000000000000 : ℝ)*(sp6) + (156279934805139/4000000000000 : ℝ)*(sp7) + (156279934805139/4000000000000 : ℝ)*(f.failure) + (7885851865829123/100000000000000 : ℝ)*(f.sum) + (16431674592923/14635000000000000000000000000 : ℝ)*base66 + (9050084446192312253/2927000000000000000000000000000000 : ℝ)*base68 + (27371943603303687747/2927000000000000000000000000000000 : ℝ)*base69 + (6355827420555687747/2927000000000000000000000000000000 : ℝ)*base71 + (14953897290449/7317500000000000000000000000 : ℝ)*base74 + (26206076824716687747/2927000000000000000000000000000000 : ℝ)*base75 + (25883959798579687747/2927000000000000000000000000000000 : ℝ)*base77 + (5051640758169687747/2927000000000000000000000000000000 : ℝ)*base79 + (12021928615977/14635000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (32977/40000000000000000000 : ℝ)*base90 + (32977/40000000000000000000 : ℝ)*base92 + (32977/40000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1216_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1216_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1216_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4073/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (587/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1216_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1216_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1216_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4073/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (587/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1216_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

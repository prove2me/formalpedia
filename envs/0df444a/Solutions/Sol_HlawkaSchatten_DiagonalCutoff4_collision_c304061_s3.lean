-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304061_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:47:50.393+00:00
-- url     : https://prove2.me/submissions/72675b8f-ef4c-4856-87a8-deded2e60faf

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c304061_s3_s3_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-54714449/500000000 : ℝ)*x 0 + (4974373021/10000000000 : ℝ)*x 1 + (790570331/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54714449/500000000 : ℝ)^133 ≤ (5428734571387/100000000000000 : ℝ)^101 := by
    have hnat : (54714449 : ℕ)^133*100000000000000^101 ≤ 5428734571387^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54714449 500000000 5428734571387 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4974373021/10000000000 : ℝ)^133 ≤ (39870845924903/100000000000000 : ℝ)^101 := by
    have hnat : (4974373021 : ℕ)^133*100000000000000^101 ≤ 39870845924903^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4974373021 10000000000 39870845924903 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (790570331/1250000000 : ℝ)^133 ≤ (13675104872401/25000000000000 : ℝ)^101 := by
    have hnat : (790570331 : ℕ)^133*25000000000000^101 ≤ 13675104872401^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790570331 1250000000 13675104872401 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-54714449/500000000 : ℝ), (4974373021/10000000000 : ℝ), (790570331/1250000000 : ℝ)] ![(5428734571387/100000000000000 : ℝ), (39870845924903/100000000000000 : ℝ), (13675104872401/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-54714449/500000000 : ℝ)|^133 ≤ (5428734571387/100000000000000 : ℝ)^101
        have hw : |(-54714449/500000000 : ℝ)|=(54714449/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4974373021/10000000000 : ℝ)|^133 ≤ (39870845924903/100000000000000 : ℝ)^101
        have hw : |(4974373021/10000000000 : ℝ)|=(4974373021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(790570331/1250000000 : ℝ)|^133 ≤ (13675104872401/25000000000000 : ℝ)^101
        have hw : |(790570331/1250000000 : ℝ)|=(790570331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s3_s3_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-836521101/5000000000 : ℝ)*x 0 + (1916745947/10000000000 : ℝ)*x 1 + (418645621/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836521101/5000000000 : ℝ)^133 ≤ (11868594497/125000000000 : ℝ)^101 := by
    have hnat : (836521101 : ℕ)^133*125000000000^101 ≤ 11868594497^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836521101 5000000000 11868594497 125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1916745947/10000000000 : ℝ)^133 ≤ (11356860037697/100000000000000 : ℝ)^101 := by
    have hnat : (1916745947 : ℕ)^133*100000000000000^101 ≤ 11356860037697^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916745947 10000000000 11356860037697 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418645621/500000000 : ℝ)^133 ≤ (79148264348827/100000000000000 : ℝ)^101 := by
    have hnat : (418645621 : ℕ)^133*100000000000000^101 ≤ 79148264348827^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418645621 500000000 79148264348827 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-836521101/5000000000 : ℝ), (1916745947/10000000000 : ℝ), (418645621/500000000 : ℝ)] ![(11868594497/125000000000 : ℝ), (11356860037697/100000000000000 : ℝ), (79148264348827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-836521101/5000000000 : ℝ)|^133 ≤ (11868594497/125000000000 : ℝ)^101
        have hw : |(-836521101/5000000000 : ℝ)|=(836521101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1916745947/10000000000 : ℝ)|^133 ≤ (11356860037697/100000000000000 : ℝ)^101
        have hw : |(1916745947/10000000000 : ℝ)|=(1916745947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(418645621/500000000 : ℝ)|^133 ≤ (79148264348827/100000000000000 : ℝ)^101
        have hw : |(418645621/500000000 : ℝ)|=(418645621/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s3_s3_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2230356133/10000000000 : ℝ)*x 0 + (-159960131/1250000000 : ℝ)*x 1 + (262445411/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2230356133/10000000000 : ℝ)^133 ≤ (1386495678821/10000000000000 : ℝ)^101 := by
    have hnat : (2230356133 : ℕ)^133*10000000000000^101 ≤ 1386495678821^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230356133 10000000000 1386495678821 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (159960131/1250000000 : ℝ)^133 ≤ (6671189525077/100000000000000 : ℝ)^101 := by
    have hnat : (159960131 : ℕ)^133*100000000000000^101 ≤ 6671189525077^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159960131 1250000000 6671189525077 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262445411/312500000 : ℝ)^133 ≤ (7946385366943/10000000000000 : ℝ)^101 := by
    have hnat : (262445411 : ℕ)^133*10000000000000^101 ≤ 7946385366943^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262445411 312500000 7946385366943 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2230356133/10000000000 : ℝ), (-159960131/1250000000 : ℝ), (262445411/312500000 : ℝ)] ![(1386495678821/10000000000000 : ℝ), (6671189525077/100000000000000 : ℝ), (7946385366943/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2230356133/10000000000 : ℝ)|^133 ≤ (1386495678821/10000000000000 : ℝ)^101
        have hw : |(2230356133/10000000000 : ℝ)|=(2230356133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-159960131/1250000000 : ℝ)|^133 ≤ (6671189525077/100000000000000 : ℝ)^101
        have hw : |(-159960131/1250000000 : ℝ)|=(159960131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262445411/312500000 : ℝ)|^133 ≤ (7946385366943/10000000000000 : ℝ)^101
        have hw : |(262445411/312500000 : ℝ)|=(262445411/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s3_s3_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (558189603/2500000000 : ℝ)*x 0 + (1115861067/1250000000 : ℝ)*x 1 + (52591/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (558189603/2500000000 : ℝ)^133 ≤ (1735578165869/12500000000000 : ℝ)^101 := by
    have hnat : (558189603 : ℕ)^133*12500000000000^101 ≤ 1735578165869^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558189603 2500000000 1735578165869 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115861067/1250000000 : ℝ)^133 ≤ (86115305297293/100000000000000 : ℝ)^101 := by
    have hnat : (1115861067 : ℕ)^133*100000000000000^101 ≤ 86115305297293^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115861067 1250000000 86115305297293 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52591/2500000000 : ℝ)^133 ≤ (69365031/100000000000000 : ℝ)^101 := by
    have hnat : (52591 : ℕ)^133*100000000000000^101 ≤ 69365031^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52591 2500000000 69365031 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(558189603/2500000000 : ℝ), (1115861067/1250000000 : ℝ), (52591/2500000000 : ℝ)] ![(1735578165869/12500000000000 : ℝ), (86115305297293/100000000000000 : ℝ), (69365031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(558189603/2500000000 : ℝ)|^133 ≤ (1735578165869/12500000000000 : ℝ)^101
        have hw : |(558189603/2500000000 : ℝ)|=(558189603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1115861067/1250000000 : ℝ)|^133 ≤ (86115305297293/100000000000000 : ℝ)^101
        have hw : |(1115861067/1250000000 : ℝ)|=(1115861067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52591/2500000000 : ℝ)|^133 ≤ (69365031/100000000000000 : ℝ)^101
        have hw : |(52591/2500000000 : ℝ)|=(52591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s3_s3_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (213399073/500000000 : ℝ)*x 0 + (6404828127/10000000000 : ℝ)*x 1 + (1972647523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213399073/500000000 : ℝ)^133 ≤ (8147142505141/25000000000000 : ℝ)^101 := by
    have hnat : (213399073 : ℕ)^133*25000000000000^101 ≤ 8147142505141^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213399073 500000000 8147142505141 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6404828127/10000000000 : ℝ)^133 ≤ (5561640579377/10000000000000 : ℝ)^101 := by
    have hnat : (6404828127 : ℕ)^133*10000000000000^101 ≤ 5561640579377^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6404828127 10000000000 5561640579377 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1972647523/10000000000 : ℝ)^133 ≤ (11795024174451/100000000000000 : ℝ)^101 := by
    have hnat : (1972647523 : ℕ)^133*100000000000000^101 ≤ 11795024174451^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972647523 10000000000 11795024174451 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213399073/500000000 : ℝ), (6404828127/10000000000 : ℝ), (1972647523/10000000000 : ℝ)] ![(8147142505141/25000000000000 : ℝ), (5561640579377/10000000000000 : ℝ), (11795024174451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213399073/500000000 : ℝ)|^133 ≤ (8147142505141/25000000000000 : ℝ)^101
        have hw : |(213399073/500000000 : ℝ)|=(213399073/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6404828127/10000000000 : ℝ)|^133 ≤ (5561640579377/10000000000000 : ℝ)^101
        have hw : |(6404828127/10000000000 : ℝ)|=(6404828127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1972647523/10000000000 : ℝ)|^133 ≤ (11795024174451/100000000000000 : ℝ)^101
        have hw : |(1972647523/10000000000 : ℝ)|=(1972647523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s3_s3_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-575725697/5000000000 : ℝ)*x 0 + (179423193/1000000000 : ℝ)*x 1 + (4371380639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (575725697/5000000000 : ℝ)^133 ≤ (5805217240853/100000000000000 : ℝ)^101 := by
    have hnat : (575725697 : ℕ)^133*100000000000000^101 ≤ 5805217240853^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575725697 5000000000 5805217240853 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179423193/1000000000 : ℝ)^133 ≤ (1041078975607/10000000000000 : ℝ)^101 := by
    have hnat : (179423193 : ℕ)^133*10000000000000^101 ≤ 1041078975607^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179423193 1000000000 1041078975607 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4371380639/5000000000 : ℝ)^133 ≤ (5236499561809/6250000000000 : ℝ)^101 := by
    have hnat : (4371380639 : ℕ)^133*6250000000000^101 ≤ 5236499561809^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371380639 5000000000 5236499561809 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-575725697/5000000000 : ℝ), (179423193/1000000000 : ℝ), (4371380639/5000000000 : ℝ)] ![(5805217240853/100000000000000 : ℝ), (1041078975607/10000000000000 : ℝ), (5236499561809/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-575725697/5000000000 : ℝ)|^133 ≤ (5805217240853/100000000000000 : ℝ)^101
        have hw : |(-575725697/5000000000 : ℝ)|=(575725697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179423193/1000000000 : ℝ)|^133 ≤ (1041078975607/10000000000000 : ℝ)^101
        have hw : |(179423193/1000000000 : ℝ)|=(179423193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4371380639/5000000000 : ℝ)|^133 ≤ (5236499561809/6250000000000 : ℝ)^101
        have hw : |(4371380639/5000000000 : ℝ)|=(4371380639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s3_s3_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (27018273/200000000 : ℝ)*x 0 + (-1563972931/10000000000 : ℝ)*x 1 + (8771530481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27018273/200000000 : ℝ)^133 ≤ (143289003243/2000000000000 : ℝ)^101 := by
    have hnat : (27018273 : ℕ)^133*2000000000000^101 ≤ 143289003243^101*200000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27018273 200000000 143289003243 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1563972931/10000000000 : ℝ)^133 ≤ (8688314305977/100000000000000 : ℝ)^101 := by
    have hnat : (1563972931 : ℕ)^133*100000000000000^101 ≤ 8688314305977^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1563972931 10000000000 8688314305977 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8771530481/10000000000 : ℝ)^133 ≤ (1682944710451/2000000000000 : ℝ)^101 := by
    have hnat : (8771530481 : ℕ)^133*2000000000000^101 ≤ 1682944710451^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8771530481 10000000000 1682944710451 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27018273/200000000 : ℝ), (-1563972931/10000000000 : ℝ), (8771530481/10000000000 : ℝ)] ![(143289003243/2000000000000 : ℝ), (8688314305977/100000000000000 : ℝ), (1682944710451/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27018273/200000000 : ℝ)|^133 ≤ (143289003243/2000000000000 : ℝ)^101
        have hw : |(27018273/200000000 : ℝ)|=(27018273/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1563972931/10000000000 : ℝ)|^133 ≤ (8688314305977/100000000000000 : ℝ)^101
        have hw : |(-1563972931/10000000000 : ℝ)|=(1563972931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8771530481/10000000000 : ℝ)|^133 ≤ (1682944710451/2000000000000 : ℝ)^101
        have hw : |(8771530481/10000000000 : ℝ)|=(8771530481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s3_s3_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7552594909/10000000000 : ℝ)*x 0 + (409855147/1000000000 : ℝ)*x 1 + (-5394487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7552594909/10000000000 : ℝ)^133 ≤ (3454961458509/5000000000000 : ℝ)^101 := by
    have hnat : (7552594909 : ℕ)^133*5000000000000^101 ≤ 3454961458509^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7552594909 10000000000 3454961458509 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409855147/1000000000 : ℝ)^133 ≤ (30895798847263/100000000000000 : ℝ)^101 := by
    have hnat : (409855147 : ℕ)^133*100000000000000^101 ≤ 30895798847263^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409855147 1000000000 30895798847263 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394487/10000000000 : ℝ)^133 ≤ (99439381/2000000000000 : ℝ)^101 := by
    have hnat : (5394487 : ℕ)^133*2000000000000^101 ≤ 99439381^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394487 10000000000 99439381 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7552594909/10000000000 : ℝ), (409855147/1000000000 : ℝ), (-5394487/10000000000 : ℝ)] ![(3454961458509/5000000000000 : ℝ), (30895798847263/100000000000000 : ℝ), (99439381/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7552594909/10000000000 : ℝ)|^133 ≤ (3454961458509/5000000000000 : ℝ)^101
        have hw : |(7552594909/10000000000 : ℝ)|=(7552594909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(409855147/1000000000 : ℝ)|^133 ≤ (30895798847263/100000000000000 : ℝ)^101
        have hw : |(409855147/1000000000 : ℝ)|=(409855147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5394487/10000000000 : ℝ)|^133 ≤ (99439381/2000000000000 : ℝ)^101
        have hw : |(-5394487/10000000000 : ℝ)|=(5394487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s3_s3_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8438205409/10000000000 : ℝ)*x 0 + (1685286031/10000000000 : ℝ)*x 1 + (899778167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8438205409/10000000000 : ℝ)^133 ≤ (999525317253/1250000000000 : ℝ)^101 := by
    have hnat : (8438205409 : ℕ)^133*1250000000000^101 ≤ 999525317253^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8438205409 10000000000 999525317253 1250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1685286031/10000000000 : ℝ)^133 ≤ (1917296671831/20000000000000 : ℝ)^101 := by
    have hnat : (1685286031 : ℕ)^133*20000000000000^101 ≤ 1917296671831^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1685286031 10000000000 1917296671831 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899778167/5000000000 : ℝ)^133 ≤ (5225745624513/50000000000000 : ℝ)^101 := by
    have hnat : (899778167 : ℕ)^133*50000000000000^101 ≤ 5225745624513^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899778167 5000000000 5225745624513 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8438205409/10000000000 : ℝ), (1685286031/10000000000 : ℝ), (899778167/5000000000 : ℝ)] ![(999525317253/1250000000000 : ℝ), (1917296671831/20000000000000 : ℝ), (5225745624513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8438205409/10000000000 : ℝ)|^133 ≤ (999525317253/1250000000000 : ℝ)^101
        have hw : |(8438205409/10000000000 : ℝ)|=(8438205409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1685286031/10000000000 : ℝ)|^133 ≤ (1917296671831/20000000000000 : ℝ)^101
        have hw : |(1685286031/10000000000 : ℝ)|=(1685286031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899778167/5000000000 : ℝ)|^133 ≤ (5225745624513/50000000000000 : ℝ)^101
        have hw : |(899778167/5000000000 : ℝ)|=(899778167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s3_s3_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-364421483/2000000000 : ℝ)*x 0 + (2536636033/5000000000 : ℝ)*x 1 + (576853007/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (364421483/2000000000 : ℝ)^133 ≤ (1328037677683/12500000000000 : ℝ)^101 := by
    have hnat : (364421483 : ℕ)^133*12500000000000^101 ≤ 1328037677683^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364421483 2000000000 1328037677683 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2536636033/5000000000 : ℝ)^133 ≤ (10229493038489/25000000000000 : ℝ)^101 := by
    have hnat : (2536636033 : ℕ)^133*25000000000000^101 ≤ 10229493038489^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536636033 5000000000 10229493038489 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (576853007/1000000000 : ℝ)^133 ≤ (48457726409139/100000000000000 : ℝ)^101 := by
    have hnat : (576853007 : ℕ)^133*100000000000000^101 ≤ 48457726409139^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576853007 1000000000 48457726409139 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-364421483/2000000000 : ℝ), (2536636033/5000000000 : ℝ), (576853007/1000000000 : ℝ)] ![(1328037677683/12500000000000 : ℝ), (10229493038489/25000000000000 : ℝ), (48457726409139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-364421483/2000000000 : ℝ)|^133 ≤ (1328037677683/12500000000000 : ℝ)^101
        have hw : |(-364421483/2000000000 : ℝ)|=(364421483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2536636033/5000000000 : ℝ)|^133 ≤ (10229493038489/25000000000000 : ℝ)^101
        have hw : |(2536636033/5000000000 : ℝ)|=(2536636033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(576853007/1000000000 : ℝ)|^133 ≤ (48457726409139/100000000000000 : ℝ)^101
        have hw : |(576853007/1000000000 : ℝ)|=(576853007/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s3_s3_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1505034033/2000000000 : ℝ)*x 0 + (-403918331/5000000000 : ℝ)*x 1 + (3761115947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1505034033/2000000000 : ℝ)^133 ≤ (68769011916993/100000000000000 : ℝ)^101 := by
    have hnat : (1505034033 : ℕ)^133*100000000000000^101 ≤ 68769011916993^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505034033 2000000000 68769011916993 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403918331/5000000000 : ℝ)^133 ≤ (113757244697/3125000000000 : ℝ)^101 := by
    have hnat : (403918331 : ℕ)^133*3125000000000^101 ≤ 113757244697^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403918331 5000000000 113757244697 3125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3761115947/10000000000 : ℝ)^133 ≤ (27590756233263/100000000000000 : ℝ)^101 := by
    have hnat : (3761115947 : ℕ)^133*100000000000000^101 ≤ 27590756233263^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3761115947 10000000000 27590756233263 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1505034033/2000000000 : ℝ), (-403918331/5000000000 : ℝ), (3761115947/10000000000 : ℝ)] ![(68769011916993/100000000000000 : ℝ), (113757244697/3125000000000 : ℝ), (27590756233263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1505034033/2000000000 : ℝ)|^133 ≤ (68769011916993/100000000000000 : ℝ)^101
        have hw : |(1505034033/2000000000 : ℝ)|=(1505034033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-403918331/5000000000 : ℝ)|^133 ≤ (113757244697/3125000000000 : ℝ)^101
        have hw : |(-403918331/5000000000 : ℝ)|=(403918331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3761115947/10000000000 : ℝ)|^133 ≤ (27590756233263/100000000000000 : ℝ)^101
        have hw : |(3761115947/10000000000 : ℝ)|=(3761115947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s3_s3_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (825175671/5000000000 : ℝ)*x 0 + (4640049607/5000000000 : ℝ)*x 1 + (-5677211/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (825175671/5000000000 : ℝ)^133 ≤ (9325665373587/100000000000000 : ℝ)^101 := by
    have hnat : (825175671 : ℕ)^133*100000000000000^101 ≤ 9325665373587^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825175671 5000000000 9325665373587 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4640049607/5000000000 : ℝ)^133 ≤ (45315029327871/50000000000000 : ℝ)^101 := by
    have hnat : (4640049607 : ℕ)^133*50000000000000^101 ≤ 45315029327871^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4640049607 5000000000 45315029327871 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5677211/2000000000 : ℝ)^133 ≤ (22137981857/50000000000000 : ℝ)^101 := by
    have hnat : (5677211 : ℕ)^133*50000000000000^101 ≤ 22137981857^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5677211 2000000000 22137981857 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(825175671/5000000000 : ℝ), (4640049607/5000000000 : ℝ), (-5677211/2000000000 : ℝ)] ![(9325665373587/100000000000000 : ℝ), (45315029327871/50000000000000 : ℝ), (22137981857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(825175671/5000000000 : ℝ)|^133 ≤ (9325665373587/100000000000000 : ℝ)^101
        have hw : |(825175671/5000000000 : ℝ)|=(825175671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4640049607/5000000000 : ℝ)|^133 ≤ (45315029327871/50000000000000 : ℝ)^101
        have hw : |(4640049607/5000000000 : ℝ)|=(4640049607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5677211/2000000000 : ℝ)|^133 ≤ (22137981857/50000000000000 : ℝ)^101
        have hw : |(-5677211/2000000000 : ℝ)|=(5677211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304061_s3_s3_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8866987519/10000000000 : ℝ)*x 0 + (337873509/2500000000 : ℝ)*x 1 + (1395339437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8866987519/10000000000 : ℝ)^133 ≤ (17071037084389/20000000000000 : ℝ)^101 := by
    have hnat : (8866987519 : ℕ)^133*20000000000000^101 ≤ 17071037084389^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8866987519 10000000000 17071037084389 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337873509/2500000000 : ℝ)^133 ≤ (1433700735879/20000000000000 : ℝ)^101 := by
    have hnat : (337873509 : ℕ)^133*20000000000000^101 ≤ 1433700735879^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337873509 2500000000 1433700735879 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1395339437/10000000000 : ℝ)^133 ≤ (146021697/1953125000 : ℝ)^101 := by
    have hnat : (1395339437 : ℕ)^133*1953125000^101 ≤ 146021697^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395339437 10000000000 146021697 1953125000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8866987519/10000000000 : ℝ), (337873509/2500000000 : ℝ), (1395339437/10000000000 : ℝ)] ![(17071037084389/20000000000000 : ℝ), (1433700735879/20000000000000 : ℝ), (146021697/1953125000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8866987519/10000000000 : ℝ)|^133 ≤ (17071037084389/20000000000000 : ℝ)^101
        have hw : |(8866987519/10000000000 : ℝ)|=(8866987519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337873509/2500000000 : ℝ)|^133 ≤ (1433700735879/20000000000000 : ℝ)^101
        have hw : |(337873509/2500000000 : ℝ)|=(337873509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1395339437/10000000000 : ℝ)|^133 ≤ (146021697/1953125000 : ℝ)^101
        have hw : |(1395339437/10000000000 : ℝ)|=(1395339437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304061_s3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((91659/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(91659/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(90201/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(90201/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8911/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8911/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5397/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5397/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(86161/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(86161/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42117/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42117/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (91659/100000 : ℝ) ^ (33/8 : ℝ) ≤ (6981879490329907019/10000000000000000000 : ℝ) := by
    have hpowers : (91659/100000 : ℝ)^33 ≤ (6981879490329907019/10000000000000000000 : ℝ)^8 := by
      have hnat : (91659 : ℕ)^33*10000000000000000000^8 ≤ 6981879490329907019^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91659 100000 6981879490329907019 10000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91659/100000 : ℝ)) (X := (6981879490329907019/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner0a : (16981879490329907019/10000000000000000000 : ℝ) ≤ (11369833955993843/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (16981879490329907019/10000000000000000000 : ℝ)^8 ≤ (11369833955993843/10000000000000000 : ℝ)^33 := by
      have hnat : (16981879490329907019 : ℕ)^8*10000000000000000^33 ≤ 11369833955993843^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16981879490329907019 10000000000000000000 11369833955993843 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11369833955993843/10000000000000000 : ℝ)) (X := (16981879490329907019/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner0b : (11981879490329907019/5000000000000000000 : ℝ) ≤ (2471970679315521/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (11981879490329907019/5000000000000000000 : ℝ)^8 ≤ (2471970679315521/2000000000000000 : ℝ)^33 := by
      have hnat : (11981879490329907019 : ℕ)^8*2000000000000000^33 ≤ 2471970679315521^33*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11981879490329907019 5000000000000000000 2471970679315521 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2471970679315521/2000000000000000 : ℝ)) (X := (11981879490329907019/5000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1369833955993843/9165900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(495009720291881/4582950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (91659/100000 : ℝ)) (alpha := (1369833955993843/9165900000000000 : ℝ)) (beta := (495009720291881/4582950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (91659/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1369833955993843/9165900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(495009720291881/4582950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (90201/100000 : ℝ) ^ (33/8 : ℝ) ≤ (65350186040519371091/100000000000000000000 : ℝ) := by
    have hpowers : (90201/100000 : ℝ)^33 ≤ (65350186040519371091/100000000000000000000 : ℝ)^8 := by
      have hnat : (90201 : ℕ)^33*100000000000000000000^8 ≤ 65350186040519371091^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        90201 100000 65350186040519371091 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (90201/100000 : ℝ)) (X := (65350186040519371091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner1a : (165350186040519371091/100000000000000000000 : ℝ) ≤ (2259313964630347/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (165350186040519371091/100000000000000000000 : ℝ)^8 ≤ (2259313964630347/2000000000000000 : ℝ)^33 := by
      have hnat : (165350186040519371091 : ℕ)^8*2000000000000000^33 ≤ 2259313964630347^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        165350186040519371091 100000000000000000000 2259313964630347 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2259313964630347/2000000000000000 : ℝ)) (X := (165350186040519371091/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner1b : (115350186040519371091/50000000000000000000 : ℝ) ≤ (3061623033410889/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (115350186040519371091/50000000000000000000 : ℝ)^8 ≤ (3061623033410889/2500000000000000 : ℝ)^33 := by
      have hnat : (115350186040519371091 : ℕ)^8*2500000000000000^33 ≤ 3061623033410889^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        115350186040519371091 50000000000000000000 3061623033410889 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3061623033410889/2500000000000000 : ℝ)) (X := (115350186040519371091/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(259313964630347/1804020000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(949922310491821/9020100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (90201/100000 : ℝ)) (alpha := (259313964630347/1804020000000000 : ℝ)) (beta := (949922310491821/9020100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (90201/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(259313964630347/1804020000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(949922310491821/9020100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (8911/10000 : ℝ) ^ (33/8 : ℝ) ≤ (31075389761628889197/50000000000000000000 : ℝ) := by
    have hpowers : (8911/10000 : ℝ)^33 ≤ (31075389761628889197/50000000000000000000 : ℝ)^8 := by
      have hnat : (8911 : ℕ)^33*50000000000000000000^8 ≤ 31075389761628889197^8*10000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8911 10000 31075389761628889197 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8911/10000 : ℝ)) (X := (31075389761628889197/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner2a : (81075389761628889197/50000000000000000000 : ℝ) ≤ (5621593893609623/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (81075389761628889197/50000000000000000000 : ℝ)^8 ≤ (5621593893609623/5000000000000000 : ℝ)^33 := by
      have hnat : (81075389761628889197 : ℕ)^8*5000000000000000^33 ≤ 5621593893609623^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81075389761628889197 50000000000000000000 5621593893609623 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5621593893609623/5000000000000000 : ℝ)) (X := (81075389761628889197/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner2b : (56075389761628889197/25000000000000000000 : ℝ) ≤ (12163267349245143/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (56075389761628889197/25000000000000000000 : ℝ)^8 ≤ (12163267349245143/10000000000000000 : ℝ)^33 := by
      have hnat : (56075389761628889197 : ℕ)^8*10000000000000000^33 ≤ 12163267349245143^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56075389761628889197 25000000000000000000 12163267349245143 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12163267349245143/10000000000000000 : ℝ)) (X := (56075389761628889197/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(32715468084717/234500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(131439937432271/1273000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (8911/10000 : ℝ)) (alpha := (32715468084717/234500000000000 : ℝ)) (beta := (131439937432271/1273000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (8911/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(32715468084717/234500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(131439937432271/1273000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-54714449/500000000 : ℝ)*X 0 0+(4974373021/10000000000 : ℝ)*X 0 1+(790570331/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-836521101/5000000000 : ℝ)*X 0 0+(1916745947/10000000000 : ℝ)*X 0 1+(418645621/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((2230356133/10000000000 : ℝ)*X 1 0+(-159960131/1250000000 : ℝ)*X 1 1+(262445411/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((558189603/2500000000 : ℝ)*X 2 0+(1115861067/1250000000 : ℝ)*X 2 1+(52591/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((213399073/500000000 : ℝ)*X 0 0+(6404828127/10000000000 : ℝ)*X 0 1+(1972647523/10000000000 : ℝ)*X 0 2+(213399073/500000000 : ℝ)*X 1 0+(6404828127/10000000000 : ℝ)*X 1 1+(1972647523/10000000000 : ℝ)*X 1 2+(213399073/500000000 : ℝ)*X 2 0+(6404828127/10000000000 : ℝ)*X 2 1+(1972647523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-575725697/5000000000 : ℝ)*X 0 0+(179423193/1000000000 : ℝ)*X 0 1+(4371380639/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((27018273/200000000 : ℝ)*X 1 0+(-1563972931/10000000000 : ℝ)*X 1 1+(8771530481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((7552594909/10000000000 : ℝ)*X 2 0+(409855147/1000000000 : ℝ)*X 2 1+(-5394487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((8438205409/10000000000 : ℝ)*X 0 0+(1685286031/10000000000 : ℝ)*X 0 1+(899778167/5000000000 : ℝ)*X 0 2+(8438205409/10000000000 : ℝ)*X 1 0+(1685286031/10000000000 : ℝ)*X 1 1+(899778167/5000000000 : ℝ)*X 1 2+(8438205409/10000000000 : ℝ)*X 2 0+(1685286031/10000000000 : ℝ)*X 2 1+(899778167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-364421483/2000000000 : ℝ)*X 0 0+(2536636033/5000000000 : ℝ)*X 0 1+(576853007/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((1505034033/2000000000 : ℝ)*X 1 0+(-403918331/5000000000 : ℝ)*X 1 1+(3761115947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((825175671/5000000000 : ℝ)*X 2 0+(4640049607/5000000000 : ℝ)*X 2 1+(-5677211/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((8866987519/10000000000 : ℝ)*X 0 0+(337873509/2500000000 : ℝ)*X 0 1+(1395339437/10000000000 : ℝ)*X 0 2+(8866987519/10000000000 : ℝ)*X 1 0+(337873509/2500000000 : ℝ)*X 1 1+(1395339437/10000000000 : ℝ)*X 1 2+(8866987519/10000000000 : ℝ)*X 2 0+(337873509/2500000000 : ℝ)*X 2 1+(1395339437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304061_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((5397/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5397/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23080919398154238584640113204437/2046493690365250000000000000000000000 : ℝ) := by norm_num
    linear_combination (17450497391/500000000000 : ℝ)*(base5) + (862264710337/1000000000000 : ℝ)*(base7) + (195321/1000000000000 : ℝ)*(base44) + (743943/1000000000000 : ℝ)*(base50) + (384949/250000000000 : ℝ)*(base60) + (490180288783/250000000000 : ℝ)*(major_s3_0) + (1960720959811/1000000000000 : ℝ)*(major_s3_1) + (490180288783/250000000000 : ℝ)*(major_s3_2) + (225409/15625000000 : ℝ)*(sp_s3_0) + (208877983727/100000000000 : ℝ)*(sp_s3_7) + (522215642003/250000000000 : ℝ)*(sp_s3_8) + (1061881879057/500000000000 : ℝ)*(sp_s3_9) + (1060050620267/500000000000 : ℝ)*(sp_s3_13) + (68499887/1000000000000 : ℝ)*(sp_s3_14) + (1292737720299/1000000000000 : ℝ)*(f.failure) + (2088862763333/1000000000000 : ℝ)*(f.sum) + (11781352573254314131/21152134500000000000000000000000 : ℝ)*base62 + (189332926694243/318250000000000000000000000 : ℝ)*base64 + (378702962229329/9020100000000000000000000000 : ℝ)*base66 + (20490565966639/58625000000000000000000000 : ℝ)*base68 + (2440913697344928167/29170476750000000000000000000000 : ℝ)*base70 + (983278234220489/2291475000000000000000000000 : ℝ)*base72 + (1595745631807999/1804020000000000000000000000 : ℝ)*base74 + (469034982555463/1145737500000000000000000000 : ℝ)*base76 + (92291321850416965331/275591115300000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (1259/12500000000000000 : ℝ)*base86 + (1259/12500000000000000 : ℝ)*base88 + (1259/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(86161/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(86161/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8907200482471409463276260385863/584712482961500000000000000000000000 : ℝ) := by norm_num
    linear_combination (170284337483/200000000000 : ℝ)*(base7) + (1139403/500000000000 : ℝ)*(base40) + (57218154437/500000000000 : ℝ)*(base53) + (76049/100000000000 : ℝ)*(base59) + (402282054529/250000000000 : ℝ)*(major_s3_0) + (402282054529/250000000000 : ℝ)*(major_s3_1) + (1494691909241/1000000000000 : ℝ)*(major_s3_2) + (4875223/1000000000000 : ℝ)*(sp_s3_0) + (1019697/40000000000 : ℝ)*(sp_s3_7) + (2337573/20000000000 : ℝ)*(sp_s3_8) + (377452188261/250000000000 : ℝ)*(sp_s3_14) + (754861121021/500000000000 : ℝ)*(sp_s3_15) + (1624275429567/1000000000000 : ℝ)*(sp_s3_16) + (1912348040411/1000000000000 : ℝ)*(sp_s3_20) + (265231588249/250000000000 : ℝ)*(f.failure) + (1624275429567/1000000000000 : ℝ)*(f.sum) + (4260428060852102953/21152134500000000000000000000000 : ℝ)*base62 + (592865257324989/1273000000000000000000000000 : ℝ)*base65 + (192923969914483/1127512500000000000000000000 : ℝ)*base66 + (44373253060747/234500000000000000000000000 : ℝ)*base69 + (24302892672781233991/116681907000000000000000000000000 : ℝ)*base71 + (210723879509153/572868750000000000000000000 : ℝ)*base72 + (7117198169347/112751250000000000000000000 : ℝ)*base74 + (2339823448623749/4582950000000000000000000000 : ℝ)*base77 + (34565173828249937039/137795557650000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (291/3125000000000000 : ℝ)*base87 + (291/3125000000000000 : ℝ)*base89 + (427/390625000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42117/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42117/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (35811163691317739441139051/3525355750000000000000000000000 : ℝ) := by norm_num
    linear_combination (694013674641/1000000000000 : ℝ)*(base7) + (165569/62500000000 : ℝ)*(base34) + (5278984511/200000000000 : ℝ)*(base40) + (165659522257/250000000000 : ℝ)*(base43) + (783705611959/500000000000 : ℝ)*(major_s3_0) + (452387891997/500000000000 : ℝ)*(major_s3_1) + (783706936511/500000000000 : ℝ)*(major_s3_2) + (21112717/500000000000 : ℝ)*(sp_s3_7) + (121684519/500000000000 : ℝ)*(sp_s3_9) + (18530597/1000000000000 : ℝ)*(sp_s3_20) + (1004216898797/1000000000000 : ℝ)*(sp_s3_21) + (1666899862363/1000000000000 : ℝ)*(sp_s3_22) + (502009202149/500000000000 : ℝ)*(sp_s3_23) + (69096634051/40000000000 : ℝ)*(sp_s3_27) + (64588959771/62500000000 : ℝ)*(f.failure) + (1666899862363/1000000000000 : ℝ)*(f.sum) + (1926646600891403229/3525355750000000000000000000000 : ℝ)*base63 + (95565195542031/636500000000000000000000000 : ℝ)*base64 + (233846221689113/751675000000000000000000000 : ℝ)*base66 + (54734566864731/58625000000000000000000000 : ℝ)*base69 + (11564753383712770681/58340953500000000000000000000000 : ℝ)*base71 + (120188988632693/1145737500000000000000000000 : ℝ)*base72 + (160447407229163/300670000000000000000000000 : ℝ)*base75 + (188755733002433/286434375000000000000000000 : ℝ)*base76 + (540064584162680909/17224444706250000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (97/1562500000000000 : ℝ)*base86 + (97/1562500000000000 : ℝ)*base88 + (97/1562500000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((91659/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(91659/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(90201/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(90201/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8911/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8911/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5397/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5397/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(86161/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(86161/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42117/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42117/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304061_s3 p hpa hpb X hX hprev2

#print axioms solution

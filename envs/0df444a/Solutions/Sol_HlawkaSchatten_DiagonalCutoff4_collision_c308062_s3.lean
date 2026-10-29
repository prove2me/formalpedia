-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308062_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:38:53.482846+00:00
-- url     : https://prove2.me/submissions/74bb649a-7259-4fd3-8dd8-1f09b83ce975

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
theorem collision_support_c308062_s3_s3_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-374073691/2000000000 : ℝ)*x 0 + (4904417929/10000000000 : ℝ)*x 1 + (-724620549/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (374073691/2000000000 : ℝ)^69 ≤ (11275390654491/100000000000000 : ℝ)^53 := by
    have hnat : (374073691 : ℕ)^69*100000000000000^53 ≤ 11275390654491^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374073691 2000000000 11275390654491 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4904417929/10000000000 : ℝ)^69 ≤ (39553044291877/100000000000000 : ℝ)^53 := by
    have hnat : (4904417929 : ℕ)^69*100000000000000^53 ≤ 39553044291877^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4904417929 10000000000 39553044291877 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (724620549/1250000000 : ℝ)^69 ≤ (24585782518237/50000000000000 : ℝ)^53 := by
    have hnat : (724620549 : ℕ)^69*50000000000000^53 ≤ 24585782518237^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      724620549 1250000000 24585782518237 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-374073691/2000000000 : ℝ), (4904417929/10000000000 : ℝ), (-724620549/1250000000 : ℝ)] ![(11275390654491/100000000000000 : ℝ), (39553044291877/100000000000000 : ℝ), (24585782518237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-374073691/2000000000 : ℝ)|^69 ≤ (11275390654491/100000000000000 : ℝ)^53
        have hw : |(-374073691/2000000000 : ℝ)|=(374073691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4904417929/10000000000 : ℝ)|^69 ≤ (39553044291877/100000000000000 : ℝ)^53
        have hw : |(4904417929/10000000000 : ℝ)|=(4904417929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-724620549/1250000000 : ℝ)|^69 ≤ (24585782518237/50000000000000 : ℝ)^53
        have hw : |(-724620549/1250000000 : ℝ)|=(724620549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s3_s3_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5190837511/10000000000 : ℝ)*x 0 + (5194505633/10000000000 : ℝ)*x 1 + (143970207/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5190837511/10000000000 : ℝ)^69 ≤ (10646610978601/25000000000000 : ℝ)^53 := by
    have hnat : (5190837511 : ℕ)^69*25000000000000^53 ≤ 10646610978601^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190837511 10000000000 10646610978601 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5194505633/10000000000 : ℝ)^69 ≤ (8525125375029/20000000000000 : ℝ)^53 := by
    have hnat : (5194505633 : ℕ)^69*20000000000000^53 ≤ 8525125375029^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194505633 10000000000 8525125375029 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (143970207/625000000 : ℝ)^69 ≤ (14787929193511/100000000000000 : ℝ)^53 := by
    have hnat : (143970207 : ℕ)^69*100000000000000^53 ≤ 14787929193511^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143970207 625000000 14787929193511 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5190837511/10000000000 : ℝ), (5194505633/10000000000 : ℝ), (143970207/625000000 : ℝ)] ![(10646610978601/25000000000000 : ℝ), (8525125375029/20000000000000 : ℝ), (14787929193511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5190837511/10000000000 : ℝ)|^69 ≤ (10646610978601/25000000000000 : ℝ)^53
        have hw : |(5190837511/10000000000 : ℝ)|=(5190837511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5194505633/10000000000 : ℝ)|^69 ≤ (8525125375029/20000000000000 : ℝ)^53
        have hw : |(5194505633/10000000000 : ℝ)|=(5194505633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(143970207/625000000 : ℝ)|^69 ≤ (14787929193511/100000000000000 : ℝ)^53
        have hw : |(143970207/625000000 : ℝ)|=(143970207/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s3_s3_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5531232601/10000000000 : ℝ)*x 0 + (5517488377/10000000000 : ℝ)*x 1 + (-1386243441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5531232601/10000000000 : ℝ)^69 ≤ (46257617094543/100000000000000 : ℝ)^53 := by
    have hnat : (5531232601 : ℕ)^69*100000000000000^53 ≤ 46257617094543^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5531232601 10000000000 46257617094543 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5517488377/10000000000 : ℝ)^69 ≤ (46108030813557/100000000000000 : ℝ)^53 := by
    have hnat : (5517488377 : ℕ)^69*100000000000000^53 ≤ 46108030813557^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517488377 10000000000 46108030813557 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1386243441/10000000000 : ℝ)^69 ≤ (3817176040323/50000000000000 : ℝ)^53 := by
    have hnat : (1386243441 : ℕ)^69*50000000000000^53 ≤ 3817176040323^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386243441 10000000000 3817176040323 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5531232601/10000000000 : ℝ), (5517488377/10000000000 : ℝ), (-1386243441/10000000000 : ℝ)] ![(46257617094543/100000000000000 : ℝ), (46108030813557/100000000000000 : ℝ), (3817176040323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5531232601/10000000000 : ℝ)|^69 ≤ (46257617094543/100000000000000 : ℝ)^53
        have hw : |(5531232601/10000000000 : ℝ)|=(5531232601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5517488377/10000000000 : ℝ)|^69 ≤ (46108030813557/100000000000000 : ℝ)^53
        have hw : |(5517488377/10000000000 : ℝ)|=(5517488377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1386243441/10000000000 : ℝ)|^69 ≤ (3817176040323/50000000000000 : ℝ)^53
        have hw : |(-1386243441/10000000000 : ℝ)|=(1386243441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s3_s3_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1444515459/10000000000 : ℝ)*x 0 + (861606607/2000000000 : ℝ)*x 1 + (-6627521901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1444515459/10000000000 : ℝ)^69 ≤ (503423447787/6250000000000 : ℝ)^53 := by
    have hnat : (1444515459 : ℕ)^69*6250000000000^53 ≤ 503423447787^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444515459 10000000000 503423447787 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (861606607/2000000000 : ℝ)^69 ≤ (8352427247619/25000000000000 : ℝ)^53 := by
    have hnat : (861606607 : ℕ)^69*25000000000000^53 ≤ 8352427247619^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861606607 2000000000 8352427247619 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6627521901/10000000000 : ℝ)^69 ≤ (3658469738877/6250000000000 : ℝ)^53 := by
    have hnat : (6627521901 : ℕ)^69*6250000000000^53 ≤ 3658469738877^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6627521901 10000000000 3658469738877 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1444515459/10000000000 : ℝ), (861606607/2000000000 : ℝ), (-6627521901/10000000000 : ℝ)] ![(503423447787/6250000000000 : ℝ), (8352427247619/25000000000000 : ℝ), (3658469738877/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1444515459/10000000000 : ℝ)|^69 ≤ (503423447787/6250000000000 : ℝ)^53
        have hw : |(-1444515459/10000000000 : ℝ)|=(1444515459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(861606607/2000000000 : ℝ)|^69 ≤ (8352427247619/25000000000000 : ℝ)^53
        have hw : |(861606607/2000000000 : ℝ)|=(861606607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6627521901/10000000000 : ℝ)|^69 ≤ (3658469738877/6250000000000 : ℝ)^53
        have hw : |(-6627521901/10000000000 : ℝ)|=(6627521901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s3_s3_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4661745367/10000000000 : ℝ)*x 0 + (-935547337/10000000000 : ℝ)*x 1 + (-1653934759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4661745367/10000000000 : ℝ)^69 ≤ (7404874933757/20000000000000 : ℝ)^53 := by
    have hnat : (4661745367 : ℕ)^69*20000000000000^53 ≤ 7404874933757^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4661745367 10000000000 7404874933757 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935547337/10000000000 : ℝ)^69 ≤ (1143889623193/25000000000000 : ℝ)^53 := by
    have hnat : (935547337 : ℕ)^69*25000000000000^53 ≤ 1143889623193^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935547337 10000000000 1143889623193 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1653934759/2500000000 : ℝ)^69 ≤ (14600016706441/25000000000000 : ℝ)^53 := by
    have hnat : (1653934759 : ℕ)^69*25000000000000^53 ≤ 14600016706441^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1653934759 2500000000 14600016706441 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4661745367/10000000000 : ℝ), (-935547337/10000000000 : ℝ), (-1653934759/2500000000 : ℝ)] ![(7404874933757/20000000000000 : ℝ), (1143889623193/25000000000000 : ℝ), (14600016706441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4661745367/10000000000 : ℝ)|^69 ≤ (7404874933757/20000000000000 : ℝ)^53
        have hw : |(4661745367/10000000000 : ℝ)|=(4661745367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-935547337/10000000000 : ℝ)|^69 ≤ (1143889623193/25000000000000 : ℝ)^53
        have hw : |(-935547337/10000000000 : ℝ)|=(935547337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1653934759/2500000000 : ℝ)|^69 ≤ (14600016706441/25000000000000 : ℝ)^53
        have hw : |(-1653934759/2500000000 : ℝ)|=(1653934759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s3_s3_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (74146211/156250000 : ℝ)*x 0 + (1282358857/2000000000 : ℝ)*x 1 + (1158186301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (74146211/156250000 : ℝ)^69 ≤ (18945619411147/50000000000000 : ℝ)^53 := by
    have hnat : (74146211 : ℕ)^69*50000000000000^53 ≤ 18945619411147^53*156250000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74146211 156250000 18945619411147 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282358857/2000000000 : ℝ)^69 ≤ (14016812802697/25000000000000 : ℝ)^53 := by
    have hnat : (1282358857 : ℕ)^69*25000000000000^53 ≤ 14016812802697^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282358857 2000000000 14016812802697 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1158186301/10000000000 : ℝ)^69 ≤ (302075497543/5000000000000 : ℝ)^53 := by
    have hnat : (1158186301 : ℕ)^69*5000000000000^53 ≤ 302075497543^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158186301 10000000000 302075497543 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(74146211/156250000 : ℝ), (1282358857/2000000000 : ℝ), (1158186301/10000000000 : ℝ)] ![(18945619411147/50000000000000 : ℝ), (14016812802697/25000000000000 : ℝ), (302075497543/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(74146211/156250000 : ℝ)|^69 ≤ (18945619411147/50000000000000 : ℝ)^53
        have hw : |(74146211/156250000 : ℝ)|=(74146211/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1282358857/2000000000 : ℝ)|^69 ≤ (14016812802697/25000000000000 : ℝ)^53
        have hw : |(1282358857/2000000000 : ℝ)|=(1282358857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1158186301/10000000000 : ℝ)|^69 ≤ (302075497543/5000000000000 : ℝ)^53
        have hw : |(1158186301/10000000000 : ℝ)|=(1158186301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s3_s3_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1002681251/2000000000 : ℝ)*x 0 + (3233530953/5000000000 : ℝ)*x 1 + (-606342243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1002681251/2000000000 : ℝ)^69 ≤ (20350589097341/50000000000000 : ℝ)^53 := by
    have hnat : (1002681251 : ℕ)^69*50000000000000^53 ≤ 20350589097341^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002681251 2000000000 20350589097341 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3233530953/5000000000 : ℝ)^69 ≤ (453577971221/800000000000 : ℝ)^53 := by
    have hnat : (3233530953 : ℕ)^69*800000000000^53 ≤ 453577971221^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3233530953 5000000000 453577971221 800000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (606342243/10000000000 : ℝ)^69 ≤ (2601575385683/100000000000000 : ℝ)^53 := by
    have hnat : (606342243 : ℕ)^69*100000000000000^53 ≤ 2601575385683^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606342243 10000000000 2601575385683 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1002681251/2000000000 : ℝ), (3233530953/5000000000 : ℝ), (-606342243/10000000000 : ℝ)] ![(20350589097341/50000000000000 : ℝ), (453577971221/800000000000 : ℝ), (2601575385683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1002681251/2000000000 : ℝ)|^69 ≤ (20350589097341/50000000000000 : ℝ)^53
        have hw : |(1002681251/2000000000 : ℝ)|=(1002681251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3233530953/5000000000 : ℝ)|^69 ≤ (453577971221/800000000000 : ℝ)^53
        have hw : |(3233530953/5000000000 : ℝ)|=(3233530953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-606342243/10000000000 : ℝ)|^69 ≤ (2601575385683/100000000000000 : ℝ)^53
        have hw : |(-606342243/10000000000 : ℝ)|=(606342243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s3_s3_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-924788023/10000000000 : ℝ)*x 0 + (4655380153/10000000000 : ℝ)*x 1 + (-6627412361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (924788023/10000000000 : ℝ)^69 ≤ (4507170547457/100000000000000 : ℝ)^53 := by
    have hnat : (924788023 : ℕ)^69*100000000000000^53 ≤ 4507170547457^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924788023 10000000000 4507170547457 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4655380153/10000000000 : ℝ)^69 ≤ (2309910822339/6250000000000 : ℝ)^53 := by
    have hnat : (4655380153 : ℕ)^69*6250000000000^53 ≤ 2309910822339^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4655380153 10000000000 2309910822339 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6627412361/10000000000 : ℝ)^69 ≤ (29267128139293/50000000000000 : ℝ)^53 := by
    have hnat : (6627412361 : ℕ)^69*50000000000000^53 ≤ 29267128139293^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6627412361 10000000000 29267128139293 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-924788023/10000000000 : ℝ), (4655380153/10000000000 : ℝ), (-6627412361/10000000000 : ℝ)] ![(4507170547457/100000000000000 : ℝ), (2309910822339/6250000000000 : ℝ), (29267128139293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-924788023/10000000000 : ℝ)|^69 ≤ (4507170547457/100000000000000 : ℝ)^53
        have hw : |(-924788023/10000000000 : ℝ)|=(924788023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4655380153/10000000000 : ℝ)|^69 ≤ (2309910822339/6250000000000 : ℝ)^53
        have hw : |(4655380153/10000000000 : ℝ)|=(4655380153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6627412361/10000000000 : ℝ)|^69 ≤ (29267128139293/50000000000000 : ℝ)^53
        have hw : |(-6627412361/10000000000 : ℝ)|=(6627412361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s3_s3_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4337922197/10000000000 : ℝ)*x 0 + (-1458070827/10000000000 : ℝ)*x 1 + (-131853041/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4337922197/10000000000 : ℝ)^69 ≤ (16855898842327/50000000000000 : ℝ)^53 := by
    have hnat : (4337922197 : ℕ)^69*50000000000000^53 ≤ 16855898842327^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4337922197 10000000000 16855898842327 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1458070827/10000000000 : ℝ)^69 ≤ (509582433079/6250000000000 : ℝ)^53 := by
    have hnat : (1458070827 : ℕ)^69*6250000000000^53 ≤ 509582433079^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458070827 10000000000 509582433079 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131853041/200000000 : ℝ)^69 ≤ (29067441684091/50000000000000 : ℝ)^53 := by
    have hnat : (131853041 : ℕ)^69*50000000000000^53 ≤ 29067441684091^53*200000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131853041 200000000 29067441684091 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4337922197/10000000000 : ℝ), (-1458070827/10000000000 : ℝ), (-131853041/200000000 : ℝ)] ![(16855898842327/50000000000000 : ℝ), (509582433079/6250000000000 : ℝ), (29067441684091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4337922197/10000000000 : ℝ)|^69 ≤ (16855898842327/50000000000000 : ℝ)^53
        have hw : |(4337922197/10000000000 : ℝ)|=(4337922197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1458070827/10000000000 : ℝ)|^69 ≤ (509582433079/6250000000000 : ℝ)^53
        have hw : |(-1458070827/10000000000 : ℝ)|=(1458070827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-131853041/200000000 : ℝ)|^69 ≤ (29067441684091/50000000000000 : ℝ)^53
        have hw : |(-131853041/200000000 : ℝ)|=(131853041/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s3_s3_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (97036323/156250000 : ℝ)*x 0 + (4948506287/10000000000 : ℝ)*x 1 + (1181276669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97036323/156250000 : ℝ)^69 ≤ (13446159399353/25000000000000 : ℝ)^53 := by
    have hnat : (97036323 : ℕ)^69*25000000000000^53 ≤ 13446159399353^53*156250000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97036323 156250000 13446159399353 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4948506287/10000000000 : ℝ)^69 ≤ (20008286833557/50000000000000 : ℝ)^53 := by
    have hnat : (4948506287 : ℕ)^69*50000000000000^53 ≤ 20008286833557^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4948506287 10000000000 20008286833557 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1181276669/10000000000 : ℝ)^69 ≤ (1549697181247/25000000000000 : ℝ)^53 := by
    have hnat : (1181276669 : ℕ)^69*25000000000000^53 ≤ 1549697181247^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181276669 10000000000 1549697181247 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(97036323/156250000 : ℝ), (4948506287/10000000000 : ℝ), (1181276669/10000000000 : ℝ)] ![(13446159399353/25000000000000 : ℝ), (20008286833557/50000000000000 : ℝ), (1549697181247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(97036323/156250000 : ℝ)|^69 ≤ (13446159399353/25000000000000 : ℝ)^53
        have hw : |(97036323/156250000 : ℝ)|=(97036323/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4948506287/10000000000 : ℝ)|^69 ≤ (20008286833557/50000000000000 : ℝ)^53
        have hw : |(4948506287/10000000000 : ℝ)|=(4948506287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1181276669/10000000000 : ℝ)|^69 ≤ (1549697181247/25000000000000 : ℝ)^53
        have hw : |(1181276669/10000000000 : ℝ)|=(1181276669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s3_s3_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1714054769/2500000000 : ℝ)*x 0 + (2291797609/5000000000 : ℝ)*x 1 + (-606570269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1714054769/2500000000 : ℝ)^69 ≤ (61178780778273/100000000000000 : ℝ)^53 := by
    have hnat : (1714054769 : ℕ)^69*100000000000000^53 ≤ 61178780778273^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714054769 2500000000 61178780778273 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2291797609/5000000000 : ℝ)^69 ≤ (3621837003301/10000000000000 : ℝ)^53 := by
    have hnat : (2291797609 : ℕ)^69*10000000000000^53 ≤ 3621837003301^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291797609 5000000000 3621837003301 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (606570269/10000000000 : ℝ)^69 ≤ (520569836893/20000000000000 : ℝ)^53 := by
    have hnat : (606570269 : ℕ)^69*20000000000000^53 ≤ 520569836893^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606570269 10000000000 520569836893 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1714054769/2500000000 : ℝ), (2291797609/5000000000 : ℝ), (-606570269/10000000000 : ℝ)] ![(61178780778273/100000000000000 : ℝ), (3621837003301/10000000000000 : ℝ), (520569836893/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1714054769/2500000000 : ℝ)|^69 ≤ (61178780778273/100000000000000 : ℝ)^53
        have hw : |(1714054769/2500000000 : ℝ)|=(1714054769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2291797609/5000000000 : ℝ)|^69 ≤ (3621837003301/10000000000000 : ℝ)^53
        have hw : |(2291797609/5000000000 : ℝ)|=(2291797609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-606570269/10000000000 : ℝ)|^69 ≤ (520569836893/20000000000000 : ℝ)^53
        have hw : |(-606570269/10000000000 : ℝ)|=(606570269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s3_s3_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-638374229/10000000000 : ℝ)*x 0 + (2773747341/5000000000 : ℝ)*x 1 + (-1485592829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (638374229/10000000000 : ℝ)^69 ≤ (278191192029/10000000000000 : ℝ)^53 := by
    have hnat : (638374229 : ℕ)^69*10000000000000^53 ≤ 278191192029^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638374229 10000000000 278191192029 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2773747341/5000000000 : ℝ)^69 ≤ (2902171976629/6250000000000 : ℝ)^53 := by
    have hnat : (2773747341 : ℕ)^69*6250000000000^53 ≤ 2902171976629^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2773747341 5000000000 2902171976629 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1485592829/2500000000 : ℝ)^69 ≤ (6347917055717/12500000000000 : ℝ)^53 := by
    have hnat : (1485592829 : ℕ)^69*12500000000000^53 ≤ 6347917055717^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1485592829 2500000000 6347917055717 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-638374229/10000000000 : ℝ), (2773747341/5000000000 : ℝ), (-1485592829/2500000000 : ℝ)] ![(278191192029/10000000000000 : ℝ), (2902171976629/6250000000000 : ℝ), (6347917055717/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-638374229/10000000000 : ℝ)|^69 ≤ (278191192029/10000000000000 : ℝ)^53
        have hw : |(-638374229/10000000000 : ℝ)|=(638374229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2773747341/5000000000 : ℝ)|^69 ≤ (2902171976629/6250000000000 : ℝ)^53
        have hw : |(2773747341/5000000000 : ℝ)|=(2773747341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1485592829/2500000000 : ℝ)|^69 ≤ (6347917055717/12500000000000 : ℝ)^53
        have hw : |(-1485592829/2500000000 : ℝ)|=(1485592829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s3_s3_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6210323771/10000000000 : ℝ)*x 0 + (-325979477/2500000000 : ℝ)*x 1 + (-1216876003/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6210323771/10000000000 : ℝ)^69 ≤ (53784627438623/100000000000000 : ℝ)^53 := by
    have hnat : (6210323771 : ℕ)^69*100000000000000^53 ≤ 53784627438623^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6210323771 10000000000 53784627438623 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325979477/2500000000 : ℝ)^69 ≤ (3524731097253/50000000000000 : ℝ)^53 := by
    have hnat : (325979477 : ℕ)^69*50000000000000^53 ≤ 3524731097253^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325979477 2500000000 3524731097253 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1216876003/2500000000 : ℝ)^69 ≤ (4895738794149/12500000000000 : ℝ)^53 := by
    have hnat : (1216876003 : ℕ)^69*12500000000000^53 ≤ 4895738794149^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216876003 2500000000 4895738794149 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6210323771/10000000000 : ℝ), (-325979477/2500000000 : ℝ), (-1216876003/2500000000 : ℝ)] ![(53784627438623/100000000000000 : ℝ), (3524731097253/50000000000000 : ℝ), (4895738794149/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6210323771/10000000000 : ℝ)|^69 ≤ (53784627438623/100000000000000 : ℝ)^53
        have hw : |(6210323771/10000000000 : ℝ)|=(6210323771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-325979477/2500000000 : ℝ)|^69 ≤ (3524731097253/50000000000000 : ℝ)^53
        have hw : |(-325979477/2500000000 : ℝ)|=(325979477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1216876003/2500000000 : ℝ)|^69 ≤ (4895738794149/12500000000000 : ℝ)^53
        have hw : |(-1216876003/2500000000 : ℝ)|=(1216876003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s3_s3_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4526379543/10000000000 : ℝ)*x 0 + (2920311489/5000000000 : ℝ)*x 1 + (1147388483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4526379543/10000000000 : ℝ)^69 ≤ (35630894972181/100000000000000 : ℝ)^53 := by
    have hnat : (4526379543 : ℕ)^69*100000000000000^53 ≤ 35630894972181^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526379543 10000000000 35630894972181 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2920311489/5000000000 : ℝ)^69 ≤ (4965423341619/10000000000000 : ℝ)^53 := by
    have hnat : (2920311489 : ℕ)^69*10000000000000^53 ≤ 4965423341619^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2920311489 5000000000 4965423341619 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147388483/5000000000 : ℝ)^69 ≤ (7357435794373/50000000000000 : ℝ)^53 := by
    have hnat : (1147388483 : ℕ)^69*50000000000000^53 ≤ 7357435794373^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147388483 5000000000 7357435794373 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4526379543/10000000000 : ℝ), (2920311489/5000000000 : ℝ), (1147388483/5000000000 : ℝ)] ![(35630894972181/100000000000000 : ℝ), (4965423341619/10000000000000 : ℝ), (7357435794373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4526379543/10000000000 : ℝ)|^69 ≤ (35630894972181/100000000000000 : ℝ)^53
        have hw : |(4526379543/10000000000 : ℝ)|=(4526379543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2920311489/5000000000 : ℝ)|^69 ≤ (4965423341619/10000000000000 : ℝ)^53
        have hw : |(2920311489/5000000000 : ℝ)|=(2920311489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1147388483/5000000000 : ℝ)|^69 ≤ (7357435794373/50000000000000 : ℝ)^53
        have hw : |(1147388483/5000000000 : ℝ)|=(1147388483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s3_s3_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1766320763/2500000000 : ℝ)*x 0 + (2127301067/5000000000 : ℝ)*x 1 + (-763211663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1766320763/2500000000 : ℝ)^69 ≤ (63618551086901/100000000000000 : ℝ)^53 := by
    have hnat : (1766320763 : ℕ)^69*100000000000000^53 ≤ 63618551086901^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1766320763 2500000000 63618551086901 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2127301067/5000000000 : ℝ)^69 ≤ (32871261668431/100000000000000 : ℝ)^53 := by
    have hnat : (2127301067 : ℕ)^69*100000000000000^53 ≤ 32871261668431^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127301067 5000000000 32871261668431 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (763211663/10000000000 : ℝ)^69 ≤ (3510187222021/100000000000000 : ℝ)^53 := by
    have hnat : (763211663 : ℕ)^69*100000000000000^53 ≤ 3510187222021^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      763211663 10000000000 3510187222021 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1766320763/2500000000 : ℝ), (2127301067/5000000000 : ℝ), (-763211663/10000000000 : ℝ)] ![(63618551086901/100000000000000 : ℝ), (32871261668431/100000000000000 : ℝ), (3510187222021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1766320763/2500000000 : ℝ)|^69 ≤ (63618551086901/100000000000000 : ℝ)^53
        have hw : |(1766320763/2500000000 : ℝ)|=(1766320763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2127301067/5000000000 : ℝ)|^69 ≤ (32871261668431/100000000000000 : ℝ)^53
        have hw : |(2127301067/5000000000 : ℝ)|=(2127301067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-763211663/10000000000 : ℝ)|^69 ≤ (3510187222021/100000000000000 : ℝ)^53
        have hw : |(-763211663/10000000000 : ℝ)|=(763211663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308062_s3 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((6951/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6951/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1741/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1741/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-26247/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-26247/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((46177/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(46177/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46531/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46531/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31043/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31043/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s3_pow0 : (6951/10000 : ℝ) ^ (17/4 : ℝ) ≤ (10657883789338355517/50000000000000000000 : ℝ) := by
    have hpowers : (6951/10000 : ℝ)^17 ≤ (10657883789338355517/50000000000000000000 : ℝ)^4 := by
      have hnat : (6951 : ℕ)^17*50000000000000000000^4 ≤ 10657883789338355517^4*10000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6951 10000 10657883789338355517 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6951/10000 : ℝ)) (X := (10657883789338355517/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner0a : (60657883789338355517/50000000000000000000 : ℝ) ≤ (2616286161414177/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (60657883789338355517/50000000000000000000 : ℝ)^4 ≤ (2616286161414177/2500000000000000 : ℝ)^17 := by
      have hnat : (60657883789338355517 : ℕ)^4*2500000000000000^17 ≤ 2616286161414177^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60657883789338355517 50000000000000000000 2616286161414177 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2616286161414177/2500000000000000 : ℝ)) (X := (60657883789338355517/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner0b : (35657883789338355517/25000000000000000000 : ℝ) ≤ (679463341615561/625000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (35657883789338355517/25000000000000000000 : ℝ)^4 ≤ (679463341615561/625000000000000 : ℝ)^17 := by
      have hnat : (35657883789338355517 : ℕ)^4*625000000000000^17 ≤ 679463341615561^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35657883789338355517 25000000000000000000 679463341615561 625000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (679463341615561/625000000000000 : ℝ)) (X := (35657883789338355517/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(116286161414177/1737750000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(101567205048067/1737750000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (6951/10000 : ℝ)) (alpha := (116286161414177/1737750000000000 : ℝ)) (beta := (101567205048067/1737750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (6951/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(116286161414177/1737750000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(101567205048067/1737750000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (1741/2500 : ℝ) ^ (17/4 : ℝ) ≤ (21485711522720943927/100000000000000000000 : ℝ) := by
    have hpowers : (1741/2500 : ℝ)^17 ≤ (21485711522720943927/100000000000000000000 : ℝ)^4 := by
      have hnat : (1741 : ℕ)^17*100000000000000000000^4 ≤ 21485711522720943927^4*2500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1741 2500 21485711522720943927 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1741/2500 : ℝ)) (X := (21485711522720943927/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner1a : (121485711522720943927/100000000000000000000 : ℝ) ≤ (5234296104532713/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (121485711522720943927/100000000000000000000 : ℝ)^4 ≤ (5234296104532713/5000000000000000 : ℝ)^17 := by
      have hnat : (121485711522720943927 : ℕ)^4*5000000000000000^17 ≤ 5234296104532713^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        121485711522720943927 100000000000000000000 5234296104532713 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5234296104532713/5000000000000000 : ℝ)) (X := (121485711522720943927/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner1b : (71485711522720943927/50000000000000000000 : ℝ) ≤ (5438751765135769/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (71485711522720943927/50000000000000000000 : ℝ)^4 ≤ (5438751765135769/5000000000000000 : ℝ)^17 := by
      have hnat : (71485711522720943927 : ℕ)^4*5000000000000000^17 ≤ 5438751765135769^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71485711522720943927 50000000000000000000 5438751765135769 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5438751765135769/5000000000000000 : ℝ)) (X := (71485711522720943927/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(234296104532713/3482000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(12778478787691/217625000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1741/2500 : ℝ)) (alpha := (234296104532713/3482000000000000 : ℝ)) (beta := (12778478787691/217625000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1741/2500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(234296104532713/3482000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(12778478787691/217625000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (26247/50000 : ℝ) ^ (17/4 : ℝ) ≤ (1615868791082714897/25000000000000000000 : ℝ) := by
    have hpowers : (26247/50000 : ℝ)^17 ≤ (1615868791082714897/25000000000000000000 : ℝ)^4 := by
      have hnat : (26247 : ℕ)^17*25000000000000000000^4 ≤ 1615868791082714897^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26247 50000 1615868791082714897 25000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26247/50000 : ℝ)) (X := (1615868791082714897/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner2a : (26615868791082714897/25000000000000000000 : ℝ) ≤ (1268557517176467/1250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (26615868791082714897/25000000000000000000 : ℝ)^4 ≤ (1268557517176467/1250000000000000 : ℝ)^17 := by
      have hnat : (26615868791082714897 : ℕ)^4*1250000000000000^17 ≤ 1268557517176467^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26615868791082714897 25000000000000000000 1268557517176467 1250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1268557517176467/1250000000000000 : ℝ)) (X := (26615868791082714897/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s3_corner2b : (14115868791082714897/12500000000000000000 : ℝ) ≤ (10290179833949067/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (14115868791082714897/12500000000000000000 : ℝ)^4 ≤ (10290179833949067/10000000000000000 : ℝ)^17 := by
      have hnat : (14115868791082714897 : ℕ)^4*10000000000000000^17 ≤ 10290179833949067^17*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14115868791082714897 12500000000000000000 10290179833949067 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10290179833949067/10000000000000000 : ℝ)) (X := (14115868791082714897/12500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(18557517176467/656175000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(47239898845777/1749800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (26247/50000 : ℝ)) (alpha := (18557517176467/656175000000000 : ℝ)) (beta := (47239898845777/1749800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (26247/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(18557517176467/656175000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(47239898845777/1749800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-374073691/2000000000 : ℝ)*X 0 0+(4904417929/10000000000 : ℝ)*X 0 1+(-724620549/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((5190837511/10000000000 : ℝ)*X 2 0+(5194505633/10000000000 : ℝ)*X 2 1+(143970207/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((5531232601/10000000000 : ℝ)*X 0 0+(5517488377/10000000000 : ℝ)*X 0 1+(-1386243441/10000000000 : ℝ)*X 0 2+(5531232601/10000000000 : ℝ)*X 1 0+(5517488377/10000000000 : ℝ)*X 1 1+(-1386243441/10000000000 : ℝ)*X 1 2+(5531232601/10000000000 : ℝ)*X 2 0+(5517488377/10000000000 : ℝ)*X 2 1+(-1386243441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1444515459/10000000000 : ℝ)*X 0 0+(861606607/2000000000 : ℝ)*X 0 1+(-6627521901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((4661745367/10000000000 : ℝ)*X 1 0+(-935547337/10000000000 : ℝ)*X 1 1+(-1653934759/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((74146211/156250000 : ℝ)*X 2 0+(1282358857/2000000000 : ℝ)*X 2 1+(1158186301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((1002681251/2000000000 : ℝ)*X 0 0+(3233530953/5000000000 : ℝ)*X 0 1+(-606342243/10000000000 : ℝ)*X 0 2+(1002681251/2000000000 : ℝ)*X 1 0+(3233530953/5000000000 : ℝ)*X 1 1+(-606342243/10000000000 : ℝ)*X 1 2+(1002681251/2000000000 : ℝ)*X 2 0+(3233530953/5000000000 : ℝ)*X 2 1+(-606342243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-924788023/10000000000 : ℝ)*X 0 0+(4655380153/10000000000 : ℝ)*X 0 1+(-6627412361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((4337922197/10000000000 : ℝ)*X 1 0+(-1458070827/10000000000 : ℝ)*X 1 1+(-131853041/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((97036323/156250000 : ℝ)*X 2 0+(4948506287/10000000000 : ℝ)*X 2 1+(1181276669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((1714054769/2500000000 : ℝ)*X 0 0+(2291797609/5000000000 : ℝ)*X 0 1+(-606570269/10000000000 : ℝ)*X 0 2+(1714054769/2500000000 : ℝ)*X 1 0+(2291797609/5000000000 : ℝ)*X 1 1+(-606570269/10000000000 : ℝ)*X 1 2+(1714054769/2500000000 : ℝ)*X 2 0+(2291797609/5000000000 : ℝ)*X 2 1+(-606570269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-638374229/10000000000 : ℝ)*X 0 0+(2773747341/5000000000 : ℝ)*X 0 1+(-1485592829/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((6210323771/10000000000 : ℝ)*X 1 0+(-325979477/2500000000 : ℝ)*X 1 1+(-1216876003/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((4526379543/10000000000 : ℝ)*X 2 0+(2920311489/5000000000 : ℝ)*X 2 1+(1147388483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((1766320763/2500000000 : ℝ)*X 0 0+(2127301067/5000000000 : ℝ)*X 0 1+(-763211663/10000000000 : ℝ)*X 0 2+(1766320763/2500000000 : ℝ)*X 1 0+(2127301067/5000000000 : ℝ)*X 1 1+(-763211663/10000000000 : ℝ)*X 1 2+(1766320763/2500000000 : ℝ)*X 2 0+(2127301067/5000000000 : ℝ)*X 2 1+(-763211663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((46177/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(46177/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (133106520204447331767531843/15232009000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8563576761/1000000000000 : ℝ)*(base39) + (2857161/1000000000000 : ℝ)*(base49) + (126133360833/1000000000000 : ℝ)*(base60) + (4566904434837/1000000000000 : ℝ)*(major_s3_0) + (4566904434837/1000000000000 : ℝ)*(major_s3_1) + (4566904434837/1000000000000 : ℝ)*(major_s3_2) + (15778151/500000000000 : ℝ)*(sp_s3_0) + (3109763958629/500000000000 : ℝ)*(sp_s3_7) + (248779122877/40000000000 : ℝ)*(sp_s3_8) + (155488011009/25000000000 : ℝ)*(sp_s3_9) + (2914220721479/1000000000000 : ℝ)*(sp_s3_13) + (25761763/1000000000000 : ℝ)*(sp_s3_14) + (53581699/500000000000 : ℝ)*(sp_s3_15) + (64794963/1000000000000 : ℝ)*(sp_s3_23) + (2914220721479/1000000000000 : ℝ)*(f.failure) + (6219585235323/1000000000000 : ℝ)*(f.sum) + (9858099589115844809/30464018000000000000000000000000 : ℝ)*base63 + (198575804035631/1749800000000000000000000000 : ℝ)*base64 + (14514816194777/54406250000000000000000000 : ℝ)*base66 + (2553038459947/3417578125000000000000000 : ℝ)*base69 + (11183851352817652267/20271433000000000000000000000000 : ℝ)*base70 + (38251375253541/289625000000000000000000000 : ℝ)*base72 + (1154121368511981/3482000000000000000000000000 : ℝ)*base75 + (167407118761483/579250000000000000000000000 : ℝ)*base77 + (235393243940385633/504237125000000000000000000000 : ℝ)*base79 + (4431/100000000000000000 : ℝ)*base86 + (4431/100000000000000000 : ℝ)*base88 + (4431/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46531/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46531/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (421463598550979124578963919477/35292564853000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11584368743/500000000000 : ℝ)*(base39) + (154731/62500000000 : ℝ)*(base60) + (4629793490837/1000000000000 : ℝ)*(major_s3_0) + (4629793490837/1000000000000 : ℝ)*(major_s3_1) + (4629793490837/1000000000000 : ℝ)*(major_s3_2) + (3228699/125000000000 : ℝ)*(sp_s3_2) + (29529/20000000000 : ℝ)*(sp_s3_6) + (28454663/500000000000 : ℝ)*(sp_s3_7) + (37424121/1000000000000 : ℝ)*(sp_s3_8) + (3152587387831/500000000000 : ℝ)*(sp_s3_14) + (6305194260867/1000000000000 : ℝ)*(sp_s3_15) + (1261041171079/200000000000 : ℝ)*(sp_s3_16) + (118167596351/40000000000 : ℝ)*(sp_s3_20) + (159930789/1000000000000 : ℝ)*(sp_s3_27) + (2954351316013/1000000000000 : ℝ)*(f.failure) + (6305231684987/1000000000000 : ℝ)*(f.sum) + (78794589630101361173/91392054000000000000000000000000 : ℝ)*base62 + (1288056438524211/1749800000000000000000000000 : ℝ)*base64 + (189757957904117/217625000000000000000000000 : ℝ)*base67 + (1028817848377741/656175000000000000000000000 : ℝ)*base68 + (831859668486411101/60814299000000000000000000000000 : ℝ)*base70 + (1102780843083029/1737750000000000000000000000 : ℝ)*base73 + (2582728910055219/3482000000000000000000000000 : ℝ)*base74 + (138403315578847/217218750000000000000000000 : ℝ)*base76 + (48308316339116669/378177843750000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (13243/100000000000000000 : ℝ)*base87 + (13243/100000000000000000 : ℝ)*base89 + (13243/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31043/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31043/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (64279502249643592594635025863/8823141213250000000000000000000000 : ℝ) := by norm_num
    linear_combination (3686779/500000000000 : ℝ)*(base11) + (34157642547/62500000000 : ℝ)*(base39) + (1637/4000000000 : ℝ)*(base40) + (374409/500000000000 : ℝ)*(base59) + (465827931327/125000000000 : ℝ)*(major_s3_0) + (465827931327/125000000000 : ℝ)*(major_s3_1) + (465827931327/125000000000 : ℝ)*(major_s3_2) + (6710439/500000000000 : ℝ)*(sp_s3_0) + (2523177/250000000000 : ℝ)*(sp_s3_2) + (30155173/1000000000000 : ℝ)*(sp_s3_9) + (2537600394341/500000000000 : ℝ)*(sp_s3_21) + (2537610791559/500000000000 : ℝ)*(sp_s3_22) + (5075181335237/1000000000000 : ℝ)*(sp_s3_23) + (118901144483/50000000000 : ℝ)*(sp_s3_27) + (118901144483/50000000000 : ℝ)*(f.failure) + (2537610791559/500000000000 : ℝ)*(f.sum) + (1328100068349934239/3808002250000000000000000000000 : ℝ)*base63 + (83387364625197/109362500000000000000000000 : ℝ)*base65 + (29340509962497/108812500000000000000000000 : ℝ)*base66 + (135901404283219/218725000000000000000000000 : ℝ)*base69 + (2008239340343318443/2533929125000000000000000000000 : ℝ)*base71 + (131660151923819/144812500000000000000000000 : ℝ)*base72 + (71745470991719/108812500000000000000000000 : ℝ)*base75 + (559227006836469/579250000000000000000000000 : ℝ)*base77 + (495386343931115587/1008474250000000000000000000000 : ℝ)*base78 + (4587/5000000000000000 : ℝ)*base86 + (4587/5000000000000000 : ℝ)*base88 + (4587/5000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((6951/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6951/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1741/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1741/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-26247/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-26247/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((46177/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(46177/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46531/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46531/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31043/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31043/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308062_s3 p hpa hpb X hX hprev2

#print axioms solution

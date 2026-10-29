-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c319086_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:32:08.061511+00:00
-- url     : https://prove2.me/submissions/c8b8639c-9dda-4843-aa13-d390f87c9a6f

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
theorem collision_support_c319086_s1_s1_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-615319121/10000000000 : ℝ)*x 0 + (-5813198961/10000000000 : ℝ)*x 1 + (1347320019/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (615319121/10000000000 : ℝ)^5 ≤ (3064612112267/100000000000000 : ℝ)^4 := by
    have hnat : (615319121 : ℕ)^5*100000000000000^4 ≤ 3064612112267^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615319121 10000000000 3064612112267 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5813198961/10000000000 : ℝ)^5 ≤ (50759692684547/100000000000000 : ℝ)^4 := by
    have hnat : (5813198961 : ℕ)^5*100000000000000^4 ≤ 50759692684547^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5813198961 10000000000 50759692684547 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347320019/2500000000 : ℝ)^5 ≤ (2885980949283/6250000000000 : ℝ)^4 := by
    have hnat : (1347320019 : ℕ)^5*6250000000000^4 ≤ 2885980949283^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347320019 2500000000 2885980949283 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-615319121/10000000000 : ℝ), (-5813198961/10000000000 : ℝ), (1347320019/2500000000 : ℝ)] ![(3064612112267/100000000000000 : ℝ), (50759692684547/100000000000000 : ℝ), (2885980949283/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-615319121/10000000000 : ℝ)|^5 ≤ (3064612112267/100000000000000 : ℝ)^4
        have hw : |(-615319121/10000000000 : ℝ)|=(615319121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5813198961/10000000000 : ℝ)|^5 ≤ (50759692684547/100000000000000 : ℝ)^4
        have hw : |(-5813198961/10000000000 : ℝ)|=(5813198961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347320019/2500000000 : ℝ)|^5 ≤ (2885980949283/6250000000000 : ℝ)^4
        have hw : |(1347320019/2500000000 : ℝ)|=(1347320019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s1_s1_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1178675197/2000000000 : ℝ)*x 0 + (655879011/2000000000 : ℝ)*x 1 + (3144487767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1178675197/2000000000 : ℝ)^5 ≤ (10327261688033/20000000000000 : ℝ)^4 := by
    have hnat : (1178675197 : ℕ)^5*20000000000000^4 ≤ 10327261688033^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178675197 2000000000 10327261688033 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655879011/2000000000 : ℝ)^5 ≤ (24816593779033/100000000000000 : ℝ)^4 := by
    have hnat : (655879011 : ℕ)^5*100000000000000^4 ≤ 24816593779033^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655879011 2000000000 24816593779033 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3144487767/10000000000 : ℝ)^5 ≤ (5886774440773/25000000000000 : ℝ)^4 := by
    have hnat : (3144487767 : ℕ)^5*25000000000000^4 ≤ 5886774440773^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3144487767 10000000000 5886774440773 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1178675197/2000000000 : ℝ), (655879011/2000000000 : ℝ), (3144487767/10000000000 : ℝ)] ![(10327261688033/20000000000000 : ℝ), (24816593779033/100000000000000 : ℝ), (5886774440773/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1178675197/2000000000 : ℝ)|^5 ≤ (10327261688033/20000000000000 : ℝ)^4
        have hw : |(1178675197/2000000000 : ℝ)|=(1178675197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655879011/2000000000 : ℝ)|^5 ≤ (24816593779033/100000000000000 : ℝ)^4
        have hw : |(655879011/2000000000 : ℝ)|=(655879011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3144487767/10000000000 : ℝ)|^5 ≤ (5886774440773/25000000000000 : ℝ)^4
        have hw : |(3144487767/10000000000 : ℝ)|=(3144487767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s1_s1_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (279309783/500000000 : ℝ)*x 0 + (-3467026053/10000000000 : ℝ)*x 1 + (-3309512707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279309783/500000000 : ℝ)^5 ≤ (48294222520377/100000000000000 : ℝ)^4 := by
    have hnat : (279309783 : ℕ)^5*100000000000000^4 ≤ 48294222520377^4*500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279309783 500000000 48294222520377 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3467026053/10000000000 : ℝ)^5 ≤ (1662747864821/6250000000000 : ℝ)^4 := by
    have hnat : (3467026053 : ℕ)^5*6250000000000^4 ≤ 1662747864821^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3467026053 10000000000 1662747864821 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3309512707/10000000000 : ℝ)^5 ≤ (1568863226673/6250000000000 : ℝ)^4 := by
    have hnat : (3309512707 : ℕ)^5*6250000000000^4 ≤ 1568863226673^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3309512707 10000000000 1568863226673 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(279309783/500000000 : ℝ), (-3467026053/10000000000 : ℝ), (-3309512707/10000000000 : ℝ)] ![(48294222520377/100000000000000 : ℝ), (1662747864821/6250000000000 : ℝ), (1568863226673/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(279309783/500000000 : ℝ)|^5 ≤ (48294222520377/100000000000000 : ℝ)^4
        have hw : |(279309783/500000000 : ℝ)|=(279309783/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3467026053/10000000000 : ℝ)|^5 ≤ (1662747864821/6250000000000 : ℝ)^4
        have hw : |(-3467026053/10000000000 : ℝ)|=(3467026053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3309512707/10000000000 : ℝ)|^5 ≤ (1568863226673/6250000000000 : ℝ)^4
        have hw : |(-3309512707/10000000000 : ℝ)|=(3309512707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s1_s1_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (270285357/625000000 : ℝ)*x 0 + (-3068331533/10000000000 : ℝ)*x 1 + (5004697767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270285357/625000000 : ℝ)^5 ≤ (35069383054269/100000000000000 : ℝ)^4 := by
    have hnat : (270285357 : ℕ)^5*100000000000000^4 ≤ 35069383054269^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270285357 625000000 35069383054269 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3068331533/10000000000 : ℝ)^5 ≤ (5709102795647/25000000000000 : ℝ)^4 := by
    have hnat : (3068331533 : ℕ)^5*25000000000000^4 ≤ 5709102795647^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3068331533 10000000000 5709102795647 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5004697767/10000000000 : ℝ)^5 ≤ (21047102876749/50000000000000 : ℝ)^4 := by
    have hnat : (5004697767 : ℕ)^5*50000000000000^4 ≤ 21047102876749^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5004697767 10000000000 21047102876749 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270285357/625000000 : ℝ), (-3068331533/10000000000 : ℝ), (5004697767/10000000000 : ℝ)] ![(35069383054269/100000000000000 : ℝ), (5709102795647/25000000000000 : ℝ), (21047102876749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270285357/625000000 : ℝ)|^5 ≤ (35069383054269/100000000000000 : ℝ)^4
        have hw : |(270285357/625000000 : ℝ)|=(270285357/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3068331533/10000000000 : ℝ)|^5 ≤ (5709102795647/25000000000000 : ℝ)^4
        have hw : |(-3068331533/10000000000 : ℝ)|=(3068331533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5004697767/10000000000 : ℝ)|^5 ≤ (21047102876749/50000000000000 : ℝ)^4
        have hw : |(5004697767/10000000000 : ℝ)|=(5004697767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s1_s1_7 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-58651881/1000000000 : ℝ)*x 0 + (-1523756877/2500000000 : ℝ)*x 1 + (1278805841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58651881/1000000000 : ℝ)^5 ≤ (721593212749/25000000000000 : ℝ)^4 := by
    have hnat : (58651881 : ℕ)^5*25000000000000^4 ≤ 721593212749^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58651881 1000000000 721593212749 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1523756877/2500000000 : ℝ)^5 ≤ (53854201072713/100000000000000 : ℝ)^4 := by
    have hnat : (1523756877 : ℕ)^5*100000000000000^4 ≤ 53854201072713^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523756877 2500000000 53854201072713 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1278805841/2500000000 : ℝ)^5 ≤ (4325942606543/10000000000000 : ℝ)^4 := by
    have hnat : (1278805841 : ℕ)^5*10000000000000^4 ≤ 4325942606543^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278805841 2500000000 4325942606543 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-58651881/1000000000 : ℝ), (-1523756877/2500000000 : ℝ), (1278805841/2500000000 : ℝ)] ![(721593212749/25000000000000 : ℝ), (53854201072713/100000000000000 : ℝ), (4325942606543/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-58651881/1000000000 : ℝ)|^5 ≤ (721593212749/25000000000000 : ℝ)^4
        have hw : |(-58651881/1000000000 : ℝ)|=(58651881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1523756877/2500000000 : ℝ)|^5 ≤ (53854201072713/100000000000000 : ℝ)^4
        have hw : |(-1523756877/2500000000 : ℝ)|=(1523756877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1278805841/2500000000 : ℝ)|^5 ≤ (4325942606543/10000000000000 : ℝ)^4
        have hw : |(1278805841/2500000000 : ℝ)|=(1278805841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s1_s1_8 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1176568143/2000000000 : ℝ)*x 0 + (3253553897/10000000000 : ℝ)*x 1 + (3182841681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1176568143/2000000000 : ℝ)^5 ≤ (51520949934751/100000000000000 : ℝ)^4 := by
    have hnat : (1176568143 : ℕ)^5*100000000000000^4 ≤ 51520949934751^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1176568143 2000000000 51520949934751 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3253553897/10000000000 : ℝ)^5 ≤ (24572396067679/100000000000000 : ℝ)^4 := by
    have hnat : (3253553897 : ℕ)^5*100000000000000^4 ≤ 24572396067679^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3253553897 10000000000 24572396067679 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3182841681/10000000000 : ℝ)^5 ≤ (11953326996257/50000000000000 : ℝ)^4 := by
    have hnat : (3182841681 : ℕ)^5*50000000000000^4 ≤ 11953326996257^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3182841681 10000000000 11953326996257 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1176568143/2000000000 : ℝ), (3253553897/10000000000 : ℝ), (3182841681/10000000000 : ℝ)] ![(51520949934751/100000000000000 : ℝ), (24572396067679/100000000000000 : ℝ), (11953326996257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1176568143/2000000000 : ℝ)|^5 ≤ (51520949934751/100000000000000 : ℝ)^4
        have hw : |(1176568143/2000000000 : ℝ)|=(1176568143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3253553897/10000000000 : ℝ)|^5 ≤ (24572396067679/100000000000000 : ℝ)^4
        have hw : |(3253553897/10000000000 : ℝ)|=(3253553897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3182841681/10000000000 : ℝ)|^5 ≤ (11953326996257/50000000000000 : ℝ)^4
        have hw : |(3182841681/10000000000 : ℝ)|=(3182841681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s1_s1_9 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1427660387/2500000000 : ℝ)*x 0 + (-420112189/1250000000 : ℝ)*x 1 + (-654836299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1427660387/2500000000 : ℝ)^5 ≤ (49642783644163/100000000000000 : ℝ)^4 := by
    have hnat : (1427660387 : ℕ)^5*100000000000000^4 ≤ 49642783644163^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1427660387 2500000000 49642783644163 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420112189/1250000000 : ℝ)^5 ≤ (1023597173117/4000000000000 : ℝ)^4 := by
    have hnat : (420112189 : ℕ)^5*4000000000000^4 ≤ 1023597173117^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420112189 1250000000 1023597173117 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654836299/2000000000 : ℝ)^5 ≤ (4953457403577/20000000000000 : ℝ)^4 := by
    have hnat : (654836299 : ℕ)^5*20000000000000^4 ≤ 4953457403577^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654836299 2000000000 4953457403577 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1427660387/2500000000 : ℝ), (-420112189/1250000000 : ℝ), (-654836299/2000000000 : ℝ)] ![(49642783644163/100000000000000 : ℝ), (1023597173117/4000000000000 : ℝ), (4953457403577/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1427660387/2500000000 : ℝ)|^5 ≤ (49642783644163/100000000000000 : ℝ)^4
        have hw : |(1427660387/2500000000 : ℝ)|=(1427660387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420112189/1250000000 : ℝ)|^5 ≤ (1023597173117/4000000000000 : ℝ)^4
        have hw : |(-420112189/1250000000 : ℝ)|=(420112189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-654836299/2000000000 : ℝ)|^5 ≤ (4953457403577/20000000000000 : ℝ)^4
        have hw : |(-654836299/2000000000 : ℝ)|=(654836299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s1_s1_13 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3880877049/10000000000 : ℝ)*x 0 + (-669828377/2500000000 : ℝ)*x 1 + (2875988947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3880877049/10000000000 : ℝ)^5 ≤ (6126216640391/20000000000000 : ℝ)^4 := by
    have hnat : (3880877049 : ℕ)^5*20000000000000^4 ≤ 6126216640391^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3880877049 10000000000 6126216640391 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (669828377/2500000000 : ℝ)^5 ≤ (19276554789393/100000000000000 : ℝ)^4 := by
    have hnat : (669828377 : ℕ)^5*100000000000000^4 ≤ 19276554789393^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669828377 2500000000 19276554789393 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2875988947/5000000000 : ℝ)^5 ≤ (5009236199499/10000000000000 : ℝ)^4 := by
    have hnat : (2875988947 : ℕ)^5*10000000000000^4 ≤ 5009236199499^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2875988947 5000000000 5009236199499 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3880877049/10000000000 : ℝ), (-669828377/2500000000 : ℝ), (2875988947/5000000000 : ℝ)] ![(6126216640391/20000000000000 : ℝ), (19276554789393/100000000000000 : ℝ), (5009236199499/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3880877049/10000000000 : ℝ)|^5 ≤ (6126216640391/20000000000000 : ℝ)^4
        have hw : |(3880877049/10000000000 : ℝ)|=(3880877049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-669828377/2500000000 : ℝ)|^5 ≤ (19276554789393/100000000000000 : ℝ)^4
        have hw : |(-669828377/2500000000 : ℝ)|=(669828377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2875988947/5000000000 : ℝ)|^5 ≤ (5009236199499/10000000000000 : ℝ)^4
        have hw : |(2875988947/5000000000 : ℝ)|=(2875988947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s1_s1_14 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-42410521/1000000000 : ℝ)*x 0 + (-1439447017/2500000000 : ℝ)*x 1 + (1387879687/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42410521/1000000000 : ℝ)^5 ≤ (481151692993/25000000000000 : ℝ)^4 := by
    have hnat : (42410521 : ℕ)^5*25000000000000^4 ≤ 481151692993^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42410521 1000000000 481151692993 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1439447017/2500000000 : ℝ)^5 ≤ (50155618948533/100000000000000 : ℝ)^4 := by
    have hnat : (1439447017 : ℕ)^5*100000000000000^4 ≤ 50155618948533^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1439447017 2500000000 50155618948533 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1387879687/2500000000 : ℝ)^5 ≤ (23959887129571/50000000000000 : ℝ)^4 := by
    have hnat : (1387879687 : ℕ)^5*50000000000000^4 ≤ 23959887129571^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387879687 2500000000 23959887129571 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42410521/1000000000 : ℝ), (-1439447017/2500000000 : ℝ), (1387879687/2500000000 : ℝ)] ![(481151692993/25000000000000 : ℝ), (50155618948533/100000000000000 : ℝ), (23959887129571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42410521/1000000000 : ℝ)|^5 ≤ (481151692993/25000000000000 : ℝ)^4
        have hw : |(-42410521/1000000000 : ℝ)|=(42410521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1439447017/2500000000 : ℝ)|^5 ≤ (50155618948533/100000000000000 : ℝ)^4
        have hw : |(-1439447017/2500000000 : ℝ)|=(1439447017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1387879687/2500000000 : ℝ)|^5 ≤ (23959887129571/50000000000000 : ℝ)^4
        have hw : |(1387879687/2500000000 : ℝ)|=(1387879687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s1_s1_15 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (6087636241/10000000000 : ℝ)*x 0 + (3237856969/10000000000 : ℝ)*x 1 + (2956752517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6087636241/10000000000 : ℝ)^5 ≤ (10754515824609/20000000000000 : ℝ)^4 := by
    have hnat : (6087636241 : ℕ)^5*20000000000000^4 ≤ 10754515824609^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6087636241 10000000000 10754515824609 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3237856969/10000000000 : ℝ)^5 ≤ (24424297153129/100000000000000 : ℝ)^4 := by
    have hnat : (3237856969 : ℕ)^5*100000000000000^4 ≤ 24424297153129^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3237856969 10000000000 24424297153129 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2956752517/10000000000 : ℝ)^5 ≤ (10901561855463/50000000000000 : ℝ)^4 := by
    have hnat : (2956752517 : ℕ)^5*50000000000000^4 ≤ 10901561855463^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956752517 10000000000 10901561855463 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6087636241/10000000000 : ℝ), (3237856969/10000000000 : ℝ), (2956752517/10000000000 : ℝ)] ![(10754515824609/20000000000000 : ℝ), (24424297153129/100000000000000 : ℝ), (10901561855463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6087636241/10000000000 : ℝ)|^5 ≤ (10754515824609/20000000000000 : ℝ)^4
        have hw : |(6087636241/10000000000 : ℝ)|=(6087636241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3237856969/10000000000 : ℝ)|^5 ≤ (24424297153129/100000000000000 : ℝ)^4
        have hw : |(3237856969/10000000000 : ℝ)|=(3237856969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2956752517/10000000000 : ℝ)|^5 ≤ (10901561855463/50000000000000 : ℝ)^4
        have hw : |(2956752517/10000000000 : ℝ)|=(2956752517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s1_s1_16 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (572057903/1000000000 : ℝ)*x 0 + (-3482973039/10000000000 : ℝ)*x 1 + (-3138621077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (572057903/1000000000 : ℝ)^5 ≤ (6218848833841/12500000000000 : ℝ)^4 := by
    have hnat : (572057903 : ℕ)^5*12500000000000^4 ≤ 6218848833841^4*1000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572057903 1000000000 6218848833841 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3482973039/10000000000 : ℝ)^5 ≤ (13378506845243/50000000000000 : ℝ)^4 := by
    have hnat : (3482973039 : ℕ)^5*50000000000000^4 ≤ 13378506845243^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3482973039 10000000000 13378506845243 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3138621077/10000000000 : ℝ)^5 ≤ (11746097810563/50000000000000 : ℝ)^4 := by
    have hnat : (3138621077 : ℕ)^5*50000000000000^4 ≤ 11746097810563^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3138621077 10000000000 11746097810563 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(572057903/1000000000 : ℝ), (-3482973039/10000000000 : ℝ), (-3138621077/10000000000 : ℝ)] ![(6218848833841/12500000000000 : ℝ), (13378506845243/50000000000000 : ℝ), (11746097810563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(572057903/1000000000 : ℝ)|^5 ≤ (6218848833841/12500000000000 : ℝ)^4
        have hw : |(572057903/1000000000 : ℝ)|=(572057903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3482973039/10000000000 : ℝ)|^5 ≤ (13378506845243/50000000000000 : ℝ)^4
        have hw : |(-3482973039/10000000000 : ℝ)|=(3482973039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3138621077/10000000000 : ℝ)|^5 ≤ (11746097810563/50000000000000 : ℝ)^4
        have hw : |(-3138621077/10000000000 : ℝ)|=(3138621077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s1_s1_20 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3968537867/10000000000 : ℝ)*x 0 + (-2824950081/10000000000 : ℝ)*x 1 + (346893287/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3968537867/10000000000 : ℝ)^5 ≤ (31498375843867/100000000000000 : ℝ)^4 := by
    have hnat : (3968537867 : ℕ)^5*100000000000000^4 ≤ 31498375843867^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3968537867 10000000000 31498375843867 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2824950081/10000000000 : ℝ)^5 ≤ (643596233863/3125000000000 : ℝ)^4 := by
    have hnat : (2824950081 : ℕ)^5*3125000000000^4 ≤ 643596233863^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2824950081 10000000000 643596233863 3125000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (346893287/625000000 : ℝ)^5 ≤ (47906544659481/100000000000000 : ℝ)^4 := by
    have hnat : (346893287 : ℕ)^5*100000000000000^4 ≤ 47906544659481^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346893287 625000000 47906544659481 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3968537867/10000000000 : ℝ), (-2824950081/10000000000 : ℝ), (346893287/625000000 : ℝ)] ![(31498375843867/100000000000000 : ℝ), (643596233863/3125000000000 : ℝ), (47906544659481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3968537867/10000000000 : ℝ)|^5 ≤ (31498375843867/100000000000000 : ℝ)^4
        have hw : |(3968537867/10000000000 : ℝ)|=(3968537867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2824950081/10000000000 : ℝ)|^5 ≤ (643596233863/3125000000000 : ℝ)^4
        have hw : |(-2824950081/10000000000 : ℝ)|=(2824950081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(346893287/625000000 : ℝ)|^5 ≤ (47906544659481/100000000000000 : ℝ)^4
        have hw : |(346893287/625000000 : ℝ)|=(346893287/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s1_s1_21 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-360312657/10000000000 : ℝ)*x 0 + (-3016812863/5000000000 : ℝ)*x 1 + (5302981561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360312657/10000000000 : ℝ)^5 ≤ (6132102879/390625000000 : ℝ)^4 := by
    have hnat : (360312657 : ℕ)^5*390625000000^4 ≤ 6132102879^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360312657 10000000000 6132102879 390625000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3016812863/5000000000 : ℝ)^5 ≤ (53176892946023/100000000000000 : ℝ)^4 := by
    have hnat : (3016812863 : ℕ)^5*100000000000000^4 ≤ 53176892946023^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3016812863 5000000000 53176892946023 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5302981561/10000000000 : ℝ)^5 ≤ (45253288705121/100000000000000 : ℝ)^4 := by
    have hnat : (5302981561 : ℕ)^5*100000000000000^4 ≤ 45253288705121^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302981561 10000000000 45253288705121 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-360312657/10000000000 : ℝ), (-3016812863/5000000000 : ℝ), (5302981561/10000000000 : ℝ)] ![(6132102879/390625000000 : ℝ), (53176892946023/100000000000000 : ℝ), (45253288705121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-360312657/10000000000 : ℝ)|^5 ≤ (6132102879/390625000000 : ℝ)^4
        have hw : |(-360312657/10000000000 : ℝ)|=(360312657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3016812863/5000000000 : ℝ)|^5 ≤ (53176892946023/100000000000000 : ℝ)^4
        have hw : |(-3016812863/5000000000 : ℝ)|=(3016812863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5302981561/10000000000 : ℝ)|^5 ≤ (45253288705121/100000000000000 : ℝ)^4
        have hw : |(5302981561/10000000000 : ℝ)|=(5302981561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s1_s1_22 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (153785719/250000000 : ℝ)*x 0 + (773728633/2500000000 : ℝ)*x 1 + (1512724233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (153785719/250000000 : ℝ)^5 ≤ (27238927441323/50000000000000 : ℝ)^4 := by
    have hnat : (153785719 : ℕ)^5*50000000000000^4 ≤ 27238927441323^4*250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153785719 250000000 27238927441323 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (773728633/2500000000 : ℝ)^5 ≤ (230839872233/1000000000000 : ℝ)^4 := by
    have hnat : (773728633 : ℕ)^5*1000000000000^4 ≤ 230839872233^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773728633 2500000000 230839872233 1000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1512724233/5000000000 : ℝ)^5 ≤ (11219078945797/50000000000000 : ℝ)^4 := by
    have hnat : (1512724233 : ℕ)^5*50000000000000^4 ≤ 11219078945797^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512724233 5000000000 11219078945797 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(153785719/250000000 : ℝ), (773728633/2500000000 : ℝ), (1512724233/5000000000 : ℝ)] ![(27238927441323/50000000000000 : ℝ), (230839872233/1000000000000 : ℝ), (11219078945797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(153785719/250000000 : ℝ)|^5 ≤ (27238927441323/50000000000000 : ℝ)^4
        have hw : |(153785719/250000000 : ℝ)|=(153785719/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(773728633/2500000000 : ℝ)|^5 ≤ (230839872233/1000000000000 : ℝ)^4
        have hw : |(773728633/2500000000 : ℝ)|=(773728633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1512724233/5000000000 : ℝ)|^5 ≤ (11219078945797/50000000000000 : ℝ)^4
        have hw : |(1512724233/5000000000 : ℝ)|=(1512724233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s1_s1_23 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5595788099/10000000000 : ℝ)*x 0 + (-3426113013/10000000000 : ℝ)*x 1 + (-834968021/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5595788099/10000000000 : ℝ)^5 ≤ (48397906406049/100000000000000 : ℝ)^4 := by
    have hnat : (5595788099 : ℕ)^5*100000000000000^4 ≤ 48397906406049^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595788099 10000000000 48397906406049 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3426113013/10000000000 : ℝ)^5 ≤ (26212117465333/100000000000000 : ℝ)^4 := by
    have hnat : (3426113013 : ℕ)^5*100000000000000^4 ≤ 26212117465333^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3426113013 10000000000 26212117465333 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834968021/2500000000 : ℝ)^5 ≤ (5077995222079/20000000000000 : ℝ)^4 := by
    have hnat : (834968021 : ℕ)^5*20000000000000^4 ≤ 5077995222079^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834968021 2500000000 5077995222079 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5595788099/10000000000 : ℝ), (-3426113013/10000000000 : ℝ), (-834968021/2500000000 : ℝ)] ![(48397906406049/100000000000000 : ℝ), (26212117465333/100000000000000 : ℝ), (5077995222079/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5595788099/10000000000 : ℝ)|^5 ≤ (48397906406049/100000000000000 : ℝ)^4
        have hw : |(5595788099/10000000000 : ℝ)|=(5595788099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3426113013/10000000000 : ℝ)|^5 ≤ (26212117465333/100000000000000 : ℝ)^4
        have hw : |(-3426113013/10000000000 : ℝ)|=(3426113013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-834968021/2500000000 : ℝ)|^5 ≤ (5077995222079/20000000000000 : ℝ)^4
        have hw : |(-834968021/2500000000 : ℝ)|=(834968021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319086_s1_s1_27 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (4305708133/10000000000 : ℝ)*x 0 + (-3097633383/10000000000 : ℝ)*x 1 + (4996908417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305708133/10000000000 : ℝ)^5 ≤ (4359791769961/12500000000000 : ℝ)^4 := by
    have hnat : (4305708133 : ℕ)^5*12500000000000^4 ≤ 4359791769961^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305708133 10000000000 4359791769961 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3097633383/10000000000 : ℝ)^5 ≤ (5777334704209/25000000000000 : ℝ)^4 := by
    have hnat : (3097633383 : ℕ)^5*25000000000000^4 ≤ 5777334704209^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3097633383 10000000000 5777334704209 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4996908417/10000000000 : ℝ)^5 ≤ (2100616350571/5000000000000 : ℝ)^4 := by
    have hnat : (4996908417 : ℕ)^5*5000000000000^4 ≤ 2100616350571^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4996908417 10000000000 2100616350571 5000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305708133/10000000000 : ℝ), (-3097633383/10000000000 : ℝ), (4996908417/10000000000 : ℝ)] ![(4359791769961/12500000000000 : ℝ), (5777334704209/25000000000000 : ℝ), (2100616350571/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305708133/10000000000 : ℝ)|^5 ≤ (4359791769961/12500000000000 : ℝ)^4
        have hw : |(4305708133/10000000000 : ℝ)|=(4305708133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3097633383/10000000000 : ℝ)|^5 ≤ (5777334704209/25000000000000 : ℝ)^4
        have hw : |(-3097633383/10000000000 : ℝ)|=(3097633383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4996908417/10000000000 : ℝ)|^5 ≤ (2100616350571/5000000000000 : ℝ)^4
        have hw : |(4996908417/10000000000 : ℝ)|=(4996908417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319086_s1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((31003/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31003/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-74177/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-74177/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9329/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9329/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7499/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7499/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-12233/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-12233/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19231/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19231/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1601/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1601/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (31003/50000 : ℝ) ^ (79/16 : ℝ) ≤ (9443684566889262779/100000000000000000000 : ℝ) := by
    have hpowers : (31003/50000 : ℝ)^79 ≤ (9443684566889262779/100000000000000000000 : ℝ)^16 := by
      have hnat : (31003 : ℕ)^79*100000000000000000000^16 ≤ 9443684566889262779^16*50000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31003 50000 9443684566889262779 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31003/50000 : ℝ)) (X := (9443684566889262779/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (109443684566889262779/100000000000000000000 : ℝ) ≤ (10184444788030743/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (109443684566889262779/100000000000000000000 : ℝ)^16 ≤ (10184444788030743/10000000000000000 : ℝ)^79 := by
      have hnat : (109443684566889262779 : ℕ)^16*10000000000000000^79 ≤ 10184444788030743^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109443684566889262779 100000000000000000000 10184444788030743 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10184444788030743/10000000000000000 : ℝ)) (X := (109443684566889262779/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (59443684566889262779/50000000000000000000 : ℝ) ≤ (10356603753296981/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (59443684566889262779/50000000000000000000 : ℝ)^16 ≤ (10356603753296981/10000000000000000 : ℝ)^79 := by
      have hnat : (59443684566889262779 : ℕ)^16*10000000000000000^79 ≤ 10356603753296981^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59443684566889262779 50000000000000000000 10356603753296981 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10356603753296981/10000000000000000 : ℝ)) (X := (59443684566889262779/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(184444788030743/6200600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(86079482633119/3100300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (31003/50000 : ℝ)) (alpha := (184444788030743/6200600000000000 : ℝ)) (beta := (86079482633119/3100300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (31003/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(184444788030743/6200600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(86079482633119/3100300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (74177/100000 : ℝ) ^ (79/16 : ℝ) ≤ (11439959828198645481/50000000000000000000 : ℝ) := by
    have hpowers : (74177/100000 : ℝ)^79 ≤ (11439959828198645481/50000000000000000000 : ℝ)^16 := by
      have hnat : (74177 : ℕ)^79*50000000000000000000^16 ≤ 11439959828198645481^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74177 100000 11439959828198645481 50000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74177/100000 : ℝ)) (X := (11439959828198645481/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (61439959828198645481/50000000000000000000 : ℝ) ≤ (5213059982731379/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (61439959828198645481/50000000000000000000 : ℝ)^16 ≤ (5213059982731379/5000000000000000 : ℝ)^79 := by
      have hnat : (61439959828198645481 : ℕ)^16*5000000000000000^79 ≤ 5213059982731379^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61439959828198645481 50000000000000000000 5213059982731379 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5213059982731379/5000000000000000 : ℝ)) (X := (61439959828198645481/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (36439959828198645481/25000000000000000000 : ℝ) ≤ (2158598370851411/2000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (36439959828198645481/25000000000000000000 : ℝ)^16 ≤ (2158598370851411/2000000000000000 : ℝ)^79 := by
      have hnat : (36439959828198645481 : ℕ)^16*2000000000000000^79 ≤ 2158598370851411^79*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36439959828198645481 25000000000000000000 2158598370851411 2000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2158598370851411/2000000000000000 : ℝ)) (X := (36439959828198645481/25000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(213059982731379/3708850000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(366871888794297/7417700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (74177/100000 : ℝ)) (alpha := (213059982731379/3708850000000000 : ℝ)) (beta := (366871888794297/7417700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (74177/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(213059982731379/3708850000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(366871888794297/7417700000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (9329/12500 : ℝ) ^ (79/16 : ℝ) ≤ (1179064564105217379/5000000000000000000 : ℝ) := by
    have hpowers : (9329/12500 : ℝ)^79 ≤ (1179064564105217379/5000000000000000000 : ℝ)^16 := by
      have hnat : (9329 : ℕ)^79*5000000000000000000^16 ≤ 1179064564105217379^16*12500^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9329 12500 1179064564105217379 5000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9329/12500 : ℝ)) (X := (1179064564105217379/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (6179064564105217379/5000000000000000000 : ℝ) ≤ (5219072643885963/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (6179064564105217379/5000000000000000000 : ℝ)^16 ≤ (5219072643885963/5000000000000000 : ℝ)^79 := by
      have hnat : (6179064564105217379 : ℕ)^16*5000000000000000^79 ≤ 5219072643885963^79*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6179064564105217379 5000000000000000000 5219072643885963 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5219072643885963/5000000000000000 : ℝ)) (X := (6179064564105217379/5000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (3679064564105217379/2500000000000000000 : ℝ) ≤ (2703487042258861/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3679064564105217379/2500000000000000000 : ℝ)^16 ≤ (2703487042258861/2500000000000000 : ℝ)^79 := by
      have hnat : (3679064564105217379 : ℕ)^16*2500000000000000^79 ≤ 2703487042258861^79*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3679064564105217379 2500000000000000000 2703487042258861 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2703487042258861/2500000000000000 : ℝ)) (X := (3679064564105217379/2500000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(219072643885963/3731600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(187901440631759/3731600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (9329/12500 : ℝ)) (alpha := (219072643885963/3731600000000000 : ℝ)) (beta := (187901440631759/3731600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (9329/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(219072643885963/3731600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(187901440631759/3731600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-615319121/10000000000 : ℝ)*X 0 0+(-5813198961/10000000000 : ℝ)*X 0 1+(1347320019/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1178675197/2000000000 : ℝ)*X 1 0+(655879011/2000000000 : ℝ)*X 1 1+(3144487767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((279309783/500000000 : ℝ)*X 2 0+(-3467026053/10000000000 : ℝ)*X 2 1+(-3309512707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((270285357/625000000 : ℝ)*X 0 0+(-3068331533/10000000000 : ℝ)*X 0 1+(5004697767/10000000000 : ℝ)*X 0 2+(270285357/625000000 : ℝ)*X 1 0+(-3068331533/10000000000 : ℝ)*X 1 1+(5004697767/10000000000 : ℝ)*X 1 2+(270285357/625000000 : ℝ)*X 2 0+(-3068331533/10000000000 : ℝ)*X 2 1+(5004697767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-58651881/1000000000 : ℝ)*X 0 0+(-1523756877/2500000000 : ℝ)*X 0 1+(1278805841/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1176568143/2000000000 : ℝ)*X 1 0+(3253553897/10000000000 : ℝ)*X 1 1+(3182841681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1427660387/2500000000 : ℝ)*X 2 0+(-420112189/1250000000 : ℝ)*X 2 1+(-654836299/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((3880877049/10000000000 : ℝ)*X 0 0+(-669828377/2500000000 : ℝ)*X 0 1+(2875988947/5000000000 : ℝ)*X 0 2+(3880877049/10000000000 : ℝ)*X 1 0+(-669828377/2500000000 : ℝ)*X 1 1+(2875988947/5000000000 : ℝ)*X 1 2+(3880877049/10000000000 : ℝ)*X 2 0+(-669828377/2500000000 : ℝ)*X 2 1+(2875988947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-42410521/1000000000 : ℝ)*X 0 0+(-1439447017/2500000000 : ℝ)*X 0 1+(1387879687/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((6087636241/10000000000 : ℝ)*X 1 0+(3237856969/10000000000 : ℝ)*X 1 1+(2956752517/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((572057903/1000000000 : ℝ)*X 2 0+(-3482973039/10000000000 : ℝ)*X 2 1+(-3138621077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3968537867/10000000000 : ℝ)*X 0 0+(-2824950081/10000000000 : ℝ)*X 0 1+(346893287/625000000 : ℝ)*X 0 2+(3968537867/10000000000 : ℝ)*X 1 0+(-2824950081/10000000000 : ℝ)*X 1 1+(346893287/625000000 : ℝ)*X 1 2+(3968537867/10000000000 : ℝ)*X 2 0+(-2824950081/10000000000 : ℝ)*X 2 1+(346893287/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-360312657/10000000000 : ℝ)*X 0 0+(-3016812863/5000000000 : ℝ)*X 0 1+(5302981561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((153785719/250000000 : ℝ)*X 1 0+(773728633/2500000000 : ℝ)*X 1 1+(1512724233/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((5595788099/10000000000 : ℝ)*X 2 0+(-3426113013/10000000000 : ℝ)*X 2 1+(-834968021/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((4305708133/10000000000 : ℝ)*X 0 0+(-3097633383/10000000000 : ℝ)*X 0 1+(4996908417/10000000000 : ℝ)*X 0 2+(4305708133/10000000000 : ℝ)*X 1 0+(-3097633383/10000000000 : ℝ)*X 1 1+(4996908417/10000000000 : ℝ)*X 1 2+(4305708133/10000000000 : ℝ)*X 2 0+(-3097633383/10000000000 : ℝ)*X 2 1+(4996908417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319086_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((7499/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7499/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (140447018245275232060465767/28922698700000000000000000000000 : ℝ) := by norm_num
    linear_combination (1529614284011/500000000000 : ℝ)*(base40) + (170417/200000000000 : ℝ)*(base50) + (48144503769/250000000000 : ℝ)*(base60) + (6060401088361/500000000000 : ℝ)*(major_s1_0) + (6060401088361/500000000000 : ℝ)*(major_s1_1) + (6060401088361/500000000000 : ℝ)*(major_s1_2) + (15146521/500000000000 : ℝ)*(sp_s1_0) + (121409993/500000000000 : ℝ)*(sp_s1_2) + (17693058701987/1000000000000 : ℝ)*(sp_s1_7) + (8846572549411/500000000000 : ℝ)*(sp_s1_8) + (17692868389141/1000000000000 : ℝ)*(sp_s1_9) + (654845763597/100000000000 : ℝ)*(sp_s1_13) + (6777939/200000000000 : ℝ)*(sp_s1_16) + (3506487/62500000000 : ℝ)*(sp_s1_21) + (654845763597/100000000000 : ℝ)*(f.failure) + (8846572549411/500000000000 : ℝ)*(f.sum) + (53171259328387537057/138399446600000000000000000000000 : ℝ)*base62 + (1793585399361199/1865800000000000000000000000 : ℝ)*base64 + (1140839596496059/1854425000000000000000000000 : ℝ)*base67 + (192008012134157/1865800000000000000000000000 : ℝ)*base68 + (490817269701725977/57845397400000000000000000000000 : ℝ)*base71 + (146962587786471/1550150000000000000000000000 : ℝ)*base72 + (306728849041137/3708850000000000000000000000 : ℝ)*base75 + (80913057981673/3100300000000000000000000000 : ℝ)*base77 + (30167327431555862383/114985476550000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1559/5000000000000000 : ℝ)*base87 + (1559/5000000000000000 : ℝ)*base89 + (1559/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-12233/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-12233/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20315647002166577419191423/3615337337500000000000000000000 : ℝ) := by norm_num
    linear_combination (477039/100000000000 : ℝ)*(base39) + (5612612999849/1000000000000 : ℝ)*(base40) + (839766998171/1000000000000 : ℝ)*(base60) + (2367838967611/125000000000 : ℝ)*(major_s1_0) + (2367838967611/125000000000 : ℝ)*(major_s1_1) + (2367838967611/125000000000 : ℝ)*(major_s1_2) + (263491533/1000000000000 : ℝ)*(sp_s1_0) + (182365609/500000000000 : ℝ)*(sp_s1_1) + (34117967/1000000000000 : ℝ)*(sp_s1_6) + (27651054504441/1000000000000 : ℝ)*(sp_s1_14) + (13825226056337/500000000000 : ℝ)*(sp_s1_15) + (13825658997987/500000000000 : ℝ)*(sp_s1_16) + (10234069494731/1000000000000 : ℝ)*(sp_s1_20) + (250576041/500000000000 : ℝ)*(sp_s1_22) + (5117051806349/500000000000 : ℝ)*(f.failure) + (13825658997987/500000000000 : ℝ)*(f.sum) + (2353104733791437237/34599861650000000000000000000000 : ℝ)*base62 + (100085017266957/233225000000000000000000000 : ℝ)*base64 + (1098728603231507/3708850000000000000000000000 : ℝ)*base67 + (105109271371/58306250000000000000000000 : ℝ)*base69 + (1647685745768434643/14461349350000000000000000000000 : ℝ)*base70 + (449800084439919/1550150000000000000000000000 : ℝ)*base72 + (894201516109483/3708850000000000000000000000 : ℝ)*base75 + (22633334047033/775075000000000000000000000 : ℝ)*base77 + (43657394008063035537/114985476550000000000000000000000 : ℝ)*base78 + (19097/25000000000000000 : ℝ)*base86 + (19097/25000000000000000 : ℝ)*base88 + (19097/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19231/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19231/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (48124230997807242009955816632099/4290798042939800000000000000000000000 : ℝ) := by norm_num
    linear_combination (1262231/500000000000 : ℝ)*(base39) + (869933157533/200000000000 : ℝ)*(base40) + (1166473/1000000000000 : ℝ)*(base50) + (3233410013/100000000000 : ℝ)*(base60) + (14365877850791/1000000000000 : ℝ)*(major_s1_0) + (14365877850791/1000000000000 : ℝ)*(major_s1_1) + (14365877850791/1000000000000 : ℝ)*(major_s1_2) + (601015457/500000000000 : ℝ)*(sp_s1_2) + (80001671/500000000000 : ℝ)*(sp_s1_7) + (45152241/250000000000 : ℝ)*(sp_s1_9) + (20970196208981/1000000000000 : ℝ)*(sp_s1_21) + (20970356212323/1000000000000 : ℝ)*(sp_s1_22) + (4193794714489/200000000000 : ℝ)*(sp_s1_23) + (1552279150139/200000000000 : ℝ)*(sp_s1_27) + (1552279150139/200000000000 : ℝ)*(f.failure) + (20970356212323/1000000000000 : ℝ)*(f.sum) + (125753395379338684313/276798893200000000000000000000000 : ℝ)*base63 + (2063005629999951/3731600000000000000000000000 : ℝ)*base65 + (2999188758364151/3708850000000000000000000000 : ℝ)*base66 + (1223047292854667/3731600000000000000000000000 : ℝ)*base68 + (679722058202514567/115690794800000000000000000000000 : ℝ)*base71 + (143294178672861/3100300000000000000000000000 : ℝ)*base72 + (478201025824613/7417700000000000000000000000 : ℝ)*base74 + (1828129947146513/6200600000000000000000000000 : ℝ)*base77 + (3681121852410292103/229970953100000000000000000000000 : ℝ)*base78 + (4033/10000000000000000 : ℝ)*base87 + (4033/10000000000000000 : ℝ)*base89 + (4033/10000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((31003/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31003/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-74177/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-74177/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9329/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9329/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7499/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7499/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-12233/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-12233/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19231/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19231/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c319086_s1 p hpa hpb X hX hprev0

#print axioms solution

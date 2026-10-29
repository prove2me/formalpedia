-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314060_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:47:45.357716+00:00
-- url     : https://prove2.me/submissions/b0e36dc5-9e22-43ce-9b55-e6572e35535e

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
theorem collision_support_c314060_s1_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-365092769/2000000000 : ℝ)*x 0 + (2129707083/5000000000 : ℝ)*x 1 + (-3110513489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (365092769/2000000000 : ℝ)^75 ≤ (1150979722803/10000000000000 : ℝ)^59 := by
    have hnat : (365092769 : ℕ)^75*10000000000000^59 ≤ 1150979722803^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365092769 2000000000 1150979722803 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2129707083/5000000000 : ℝ)^75 ≤ (33793609531113/100000000000000 : ℝ)^59 := by
    have hnat : (2129707083 : ℕ)^75*100000000000000^59 ≤ 33793609531113^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129707083 5000000000 33793609531113 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3110513489/5000000000 : ℝ)^75 ≤ (6837074153121/12500000000000 : ℝ)^59 := by
    have hnat : (3110513489 : ℕ)^75*12500000000000^59 ≤ 6837074153121^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3110513489 5000000000 6837074153121 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-365092769/2000000000 : ℝ), (2129707083/5000000000 : ℝ), (-3110513489/5000000000 : ℝ)] ![(1150979722803/10000000000000 : ℝ), (33793609531113/100000000000000 : ℝ), (6837074153121/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-365092769/2000000000 : ℝ)|^75 ≤ (1150979722803/10000000000000 : ℝ)^59
        have hw : |(-365092769/2000000000 : ℝ)|=(365092769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2129707083/5000000000 : ℝ)|^75 ≤ (33793609531113/100000000000000 : ℝ)^59
        have hw : |(2129707083/5000000000 : ℝ)|=(2129707083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3110513489/5000000000 : ℝ)|^75 ≤ (6837074153121/12500000000000 : ℝ)^59
        have hw : |(-3110513489/5000000000 : ℝ)|=(3110513489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314060_s1_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (898461641/2000000000 : ℝ)*x 0 + (-1024805359/5000000000 : ℝ)*x 1 + (-2921412231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898461641/2000000000 : ℝ)^75 ≤ (36159631592937/100000000000000 : ℝ)^59 := by
    have hnat : (898461641 : ℕ)^75*100000000000000^59 ≤ 36159631592937^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898461641 2000000000 36159631592937 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024805359/5000000000 : ℝ)^75 ≤ (13335398430397/100000000000000 : ℝ)^59 := by
    have hnat : (1024805359 : ℕ)^75*100000000000000^59 ≤ 13335398430397^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024805359 5000000000 13335398430397 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2921412231/5000000000 : ℝ)^75 ≤ (3156560622859/6250000000000 : ℝ)^59 := by
    have hnat : (2921412231 : ℕ)^75*6250000000000^59 ≤ 3156560622859^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2921412231 5000000000 3156560622859 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(898461641/2000000000 : ℝ), (-1024805359/5000000000 : ℝ), (-2921412231/5000000000 : ℝ)] ![(36159631592937/100000000000000 : ℝ), (13335398430397/100000000000000 : ℝ), (3156560622859/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(898461641/2000000000 : ℝ)|^75 ≤ (36159631592937/100000000000000 : ℝ)^59
        have hw : |(898461641/2000000000 : ℝ)|=(898461641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1024805359/5000000000 : ℝ)|^75 ≤ (13335398430397/100000000000000 : ℝ)^59
        have hw : |(-1024805359/5000000000 : ℝ)|=(1024805359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2921412231/5000000000 : ℝ)|^75 ≤ (3156560622859/6250000000000 : ℝ)^59
        have hw : |(-2921412231/5000000000 : ℝ)|=(2921412231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314060_s1_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1171172801/2500000000 : ℝ)*x 0 + (1493418881/2500000000 : ℝ)*x 1 + (1623170419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1171172801/2500000000 : ℝ)^75 ≤ (3813942255829/10000000000000 : ℝ)^59 := by
    have hnat : (1171172801 : ℕ)^75*10000000000000^59 ≤ 3813942255829^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171172801 2500000000 3813942255829 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1493418881/2500000000 : ℝ)^75 ≤ (51947110194517/100000000000000 : ℝ)^59 := by
    have hnat : (1493418881 : ℕ)^75*100000000000000^59 ≤ 51947110194517^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493418881 2500000000 51947110194517 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1623170419/10000000000 : ℝ)^75 ≤ (309795851091/3125000000000 : ℝ)^59 := by
    have hnat : (1623170419 : ℕ)^75*3125000000000^59 ≤ 309795851091^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1623170419 10000000000 309795851091 3125000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1171172801/2500000000 : ℝ), (1493418881/2500000000 : ℝ), (1623170419/10000000000 : ℝ)] ![(3813942255829/10000000000000 : ℝ), (51947110194517/100000000000000 : ℝ), (309795851091/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1171172801/2500000000 : ℝ)|^75 ≤ (3813942255829/10000000000000 : ℝ)^59
        have hw : |(1171172801/2500000000 : ℝ)|=(1171172801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1493418881/2500000000 : ℝ)|^75 ≤ (51947110194517/100000000000000 : ℝ)^59
        have hw : |(1493418881/2500000000 : ℝ)|=(1493418881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1623170419/10000000000 : ℝ)|^75 ≤ (309795851091/3125000000000 : ℝ)^59
        have hw : |(1623170419/10000000000 : ℝ)|=(1623170419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314060_s1_s1_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1867239563/10000000000 : ℝ)*x 0 + (3449159289/10000000000 : ℝ)*x 1 + (-1378546161/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1867239563/10000000000 : ℝ)^75 ≤ (2961415753577/25000000000000 : ℝ)^59 := by
    have hnat : (1867239563 : ℕ)^75*25000000000000^59 ≤ 2961415753577^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867239563 10000000000 2961415753577 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3449159289/10000000000 : ℝ)^75 ≤ (3230407920983/12500000000000 : ℝ)^59 := by
    have hnat : (3449159289 : ℕ)^75*12500000000000^59 ≤ 3230407920983^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3449159289 10000000000 3230407920983 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1378546161/2000000000 : ℝ)^75 ≤ (3115553680181/5000000000000 : ℝ)^59 := by
    have hnat : (1378546161 : ℕ)^75*5000000000000^59 ≤ 3115553680181^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378546161 2000000000 3115553680181 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1867239563/10000000000 : ℝ), (3449159289/10000000000 : ℝ), (-1378546161/2000000000 : ℝ)] ![(2961415753577/25000000000000 : ℝ), (3230407920983/12500000000000 : ℝ), (3115553680181/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1867239563/10000000000 : ℝ)|^75 ≤ (2961415753577/25000000000000 : ℝ)^59
        have hw : |(-1867239563/10000000000 : ℝ)|=(1867239563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3449159289/10000000000 : ℝ)|^75 ≤ (3230407920983/12500000000000 : ℝ)^59
        have hw : |(3449159289/10000000000 : ℝ)|=(3449159289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1378546161/2000000000 : ℝ)|^75 ≤ (3115553680181/5000000000000 : ℝ)^59
        have hw : |(-1378546161/2000000000 : ℝ)|=(1378546161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314060_s1_s1_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (952781241/2500000000 : ℝ)*x 0 + (-713336951/5000000000 : ℝ)*x 1 + (-6887205531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (952781241/2500000000 : ℝ)^75 ≤ (14669337449611/50000000000000 : ℝ)^59 := by
    have hnat : (952781241 : ℕ)^75*50000000000000^59 ≤ 14669337449611^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952781241 2500000000 14669337449611 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (713336951/5000000000 : ℝ)^75 ≤ (1682747842691/20000000000000 : ℝ)^59 := by
    have hnat : (713336951 : ℕ)^75*20000000000000^59 ≤ 1682747842691^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713336951 5000000000 1682747842691 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6887205531/10000000000 : ℝ)^75 ≤ (62247585877647/100000000000000 : ℝ)^59 := by
    have hnat : (6887205531 : ℕ)^75*100000000000000^59 ≤ 62247585877647^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6887205531 10000000000 62247585877647 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(952781241/2500000000 : ℝ), (-713336951/5000000000 : ℝ), (-6887205531/10000000000 : ℝ)] ![(14669337449611/50000000000000 : ℝ), (1682747842691/20000000000000 : ℝ), (62247585877647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(952781241/2500000000 : ℝ)|^75 ≤ (14669337449611/50000000000000 : ℝ)^59
        have hw : |(952781241/2500000000 : ℝ)|=(952781241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-713336951/5000000000 : ℝ)|^75 ≤ (1682747842691/20000000000000 : ℝ)^59
        have hw : |(-713336951/5000000000 : ℝ)|=(713336951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6887205531/10000000000 : ℝ)|^75 ≤ (62247585877647/100000000000000 : ℝ)^59
        have hw : |(-6887205531/10000000000 : ℝ)|=(6887205531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314060_s1_s1_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4016930171/10000000000 : ℝ)*x 0 + (6916941679/10000000000 : ℝ)*x 1 + (1099696573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4016930171/10000000000 : ℝ)^75 ≤ (3136720212173/10000000000000 : ℝ)^59 := by
    have hnat : (4016930171 : ℕ)^75*10000000000000^59 ≤ 3136720212173^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016930171 10000000000 3136720212173 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6916941679/10000000000 : ℝ)^75 ≤ (62589429390037/100000000000000 : ℝ)^59 := by
    have hnat : (6916941679 : ℕ)^75*100000000000000^59 ≤ 62589429390037^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6916941679 10000000000 62589429390037 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099696573/10000000000 : ℝ)^75 ≤ (3021684233143/50000000000000 : ℝ)^59 := by
    have hnat : (1099696573 : ℕ)^75*50000000000000^59 ≤ 3021684233143^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099696573 10000000000 3021684233143 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4016930171/10000000000 : ℝ), (6916941679/10000000000 : ℝ), (1099696573/10000000000 : ℝ)] ![(3136720212173/10000000000000 : ℝ), (62589429390037/100000000000000 : ℝ), (3021684233143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4016930171/10000000000 : ℝ)|^75 ≤ (3136720212173/10000000000000 : ℝ)^59
        have hw : |(4016930171/10000000000 : ℝ)|=(4016930171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6916941679/10000000000 : ℝ)|^75 ≤ (62589429390037/100000000000000 : ℝ)^59
        have hw : |(6916941679/10000000000 : ℝ)|=(6916941679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1099696573/10000000000 : ℝ)|^75 ≤ (3021684233143/50000000000000 : ℝ)^59
        have hw : |(1099696573/10000000000 : ℝ)|=(1099696573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314060_s1_s1_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (89632053/156250000 : ℝ)*x 0 + (1171122153/2000000000 : ℝ)*x 1 + (-2512061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (89632053/156250000 : ℝ)^75 ≤ (3083689739457/6250000000000 : ℝ)^59 := by
    have hnat : (89632053 : ℕ)^75*6250000000000^59 ≤ 3083689739457^59*156250000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89632053 156250000 3083689739457 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1171122153/2000000000 : ℝ)^75 ≤ (25322754069169/50000000000000 : ℝ)^59 := by
    have hnat : (1171122153 : ℕ)^75*50000000000000^59 ≤ 25322754069169^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171122153 2000000000 25322754069169 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2512061/2500000000 : ℝ)^75 ≤ (7728010103/50000000000000 : ℝ)^59 := by
    have hnat : (2512061 : ℕ)^75*50000000000000^59 ≤ 7728010103^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512061 2500000000 7728010103 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(89632053/156250000 : ℝ), (1171122153/2000000000 : ℝ), (-2512061/2500000000 : ℝ)] ![(3083689739457/6250000000000 : ℝ), (25322754069169/50000000000000 : ℝ), (7728010103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(89632053/156250000 : ℝ)|^75 ≤ (3083689739457/6250000000000 : ℝ)^59
        have hw : |(89632053/156250000 : ℝ)|=(89632053/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1171122153/2000000000 : ℝ)|^75 ≤ (25322754069169/50000000000000 : ℝ)^59
        have hw : |(1171122153/2000000000 : ℝ)|=(1171122153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2512061/2500000000 : ℝ)|^75 ≤ (7728010103/50000000000000 : ℝ)^59
        have hw : |(-2512061/2500000000 : ℝ)|=(2512061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314060_s1_s1_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1127438581/10000000000 : ℝ)*x 0 + (46624559/125000000 : ℝ)*x 1 + (-714423149/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1127438581/10000000000 : ℝ)^75 ≤ (311891358497/5000000000000 : ℝ)^59 := by
    have hnat : (1127438581 : ℕ)^75*5000000000000^59 ≤ 311891358497^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127438581 10000000000 311891358497 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46624559/125000000 : ℝ)^75 ≤ (5709352378157/20000000000000 : ℝ)^59 := by
    have hnat : (46624559 : ℕ)^75*20000000000000^59 ≤ 5709352378157^59*125000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46624559 125000000 5709352378157 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (714423149/1000000000 : ℝ)^75 ≤ (13043082183999/20000000000000 : ℝ)^59 := by
    have hnat : (714423149 : ℕ)^75*20000000000000^59 ≤ 13043082183999^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714423149 1000000000 13043082183999 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1127438581/10000000000 : ℝ), (46624559/125000000 : ℝ), (-714423149/1000000000 : ℝ)] ![(311891358497/5000000000000 : ℝ), (5709352378157/20000000000000 : ℝ), (13043082183999/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1127438581/10000000000 : ℝ)|^75 ≤ (311891358497/5000000000000 : ℝ)^59
        have hw : |(-1127438581/10000000000 : ℝ)|=(1127438581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46624559/125000000 : ℝ)|^75 ≤ (5709352378157/20000000000000 : ℝ)^59
        have hw : |(46624559/125000000 : ℝ)|=(46624559/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-714423149/1000000000 : ℝ)|^75 ≤ (13043082183999/20000000000000 : ℝ)^59
        have hw : |(-714423149/1000000000 : ℝ)|=(714423149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314060_s1_s1_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1640901771/5000000000 : ℝ)*x 0 + (-854929867/5000000000 : ℝ)*x 1 + (-7138490069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1640901771/5000000000 : ℝ)^75 ≤ (1516243281347/6250000000000 : ℝ)^59 := by
    have hnat : (1640901771 : ℕ)^75*6250000000000^59 ≤ 1516243281347^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1640901771 5000000000 1516243281347 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (854929867/5000000000 : ℝ)^75 ≤ (5295656091169/50000000000000 : ℝ)^59 := by
    have hnat : (854929867 : ℕ)^75*50000000000000^59 ≤ 5295656091169^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854929867 5000000000 5295656091169 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7138490069/10000000000 : ℝ)^75 ≤ (8143599413431/12500000000000 : ℝ)^59 := by
    have hnat : (7138490069 : ℕ)^75*12500000000000^59 ≤ 8143599413431^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7138490069 10000000000 8143599413431 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1640901771/5000000000 : ℝ), (-854929867/5000000000 : ℝ), (-7138490069/10000000000 : ℝ)] ![(1516243281347/6250000000000 : ℝ), (5295656091169/50000000000000 : ℝ), (8143599413431/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1640901771/5000000000 : ℝ)|^75 ≤ (1516243281347/6250000000000 : ℝ)^59
        have hw : |(1640901771/5000000000 : ℝ)|=(1640901771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-854929867/5000000000 : ℝ)|^75 ≤ (5295656091169/50000000000000 : ℝ)^59
        have hw : |(-854929867/5000000000 : ℝ)|=(854929867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7138490069/10000000000 : ℝ)|^75 ≤ (8143599413431/12500000000000 : ℝ)^59
        have hw : |(-7138490069/10000000000 : ℝ)|=(7138490069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314060_s1_s1_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3053026033/5000000000 : ℝ)*x 0 + (4876792341/10000000000 : ℝ)*x 1 + (144629959/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3053026033/5000000000 : ℝ)^75 ≤ (26707403073539/50000000000000 : ℝ)^59 := by
    have hnat : (3053026033 : ℕ)^75*50000000000000^59 ≤ 26707403073539^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3053026033 5000000000 26707403073539 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4876792341/10000000000 : ℝ)^75 ≤ (1605537654481/4000000000000 : ℝ)^59 := by
    have hnat : (4876792341 : ℕ)^75*4000000000000^59 ≤ 1605537654481^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4876792341 10000000000 1605537654481 4000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (144629959/1250000000 : ℝ)^75 ≤ (3223376238987/50000000000000 : ℝ)^59 := by
    have hnat : (144629959 : ℕ)^75*50000000000000^59 ≤ 3223376238987^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144629959 1250000000 3223376238987 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3053026033/5000000000 : ℝ), (4876792341/10000000000 : ℝ), (144629959/1250000000 : ℝ)] ![(26707403073539/50000000000000 : ℝ), (1605537654481/4000000000000 : ℝ), (3223376238987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3053026033/5000000000 : ℝ)|^75 ≤ (26707403073539/50000000000000 : ℝ)^59
        have hw : |(3053026033/5000000000 : ℝ)|=(3053026033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4876792341/10000000000 : ℝ)|^75 ≤ (1605537654481/4000000000000 : ℝ)^59
        have hw : |(4876792341/10000000000 : ℝ)|=(4876792341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(144629959/1250000000 : ℝ)|^75 ≤ (3223376238987/50000000000000 : ℝ)^59
        have hw : |(144629959/1250000000 : ℝ)|=(144629959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314060_s1_s1_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4023848717/5000000000 : ℝ)*x 0 + (130403019/400000000 : ℝ)*x 1 + (-4141617/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4023848717/5000000000 : ℝ)^75 ≤ (9484208236531/12500000000000 : ℝ)^59 := by
    have hnat : (4023848717 : ℕ)^75*12500000000000^59 ≤ 9484208236531^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023848717 5000000000 9484208236531 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130403019/400000000 : ℝ)^75 ≤ (12027949589451/50000000000000 : ℝ)^59 := by
    have hnat : (130403019 : ℕ)^75*50000000000000^59 ≤ 12027949589451^59*400000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130403019 400000000 12027949589451 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4141617/1250000000 : ℝ)^75 ≤ (70434921667/100000000000000 : ℝ)^59 := by
    have hnat : (4141617 : ℕ)^75*100000000000000^59 ≤ 70434921667^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141617 1250000000 70434921667 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4023848717/5000000000 : ℝ), (130403019/400000000 : ℝ), (-4141617/1250000000 : ℝ)] ![(9484208236531/12500000000000 : ℝ), (12027949589451/50000000000000 : ℝ), (70434921667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4023848717/5000000000 : ℝ)|^75 ≤ (9484208236531/12500000000000 : ℝ)^59
        have hw : |(4023848717/5000000000 : ℝ)|=(4023848717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130403019/400000000 : ℝ)|^75 ≤ (12027949589451/50000000000000 : ℝ)^59
        have hw : |(130403019/400000000 : ℝ)|=(130403019/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4141617/1250000000 : ℝ)|^75 ≤ (70434921667/100000000000000 : ℝ)^59
        have hw : |(-4141617/1250000000 : ℝ)|=(4141617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314060_s1_s1_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-324826143/5000000000 : ℝ)*x 0 + (5645147131/10000000000 : ℝ)*x 1 + (-566524479/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324826143/5000000000 : ℝ)^75 ≤ (619050594811/20000000000000 : ℝ)^59 := by
    have hnat : (324826143 : ℕ)^75*20000000000000^59 ≤ 619050594811^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324826143 5000000000 619050594811 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5645147131/10000000000 : ℝ)^75 ≤ (48342929532443/100000000000000 : ℝ)^59 := by
    have hnat : (5645147131 : ℕ)^75*100000000000000^59 ≤ 48342929532443^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5645147131 10000000000 48342929532443 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566524479/1000000000 : ℝ)^75 ≤ (6070227184519/12500000000000 : ℝ)^59 := by
    have hnat : (566524479 : ℕ)^75*12500000000000^59 ≤ 6070227184519^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566524479 1000000000 6070227184519 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-324826143/5000000000 : ℝ), (5645147131/10000000000 : ℝ), (-566524479/1000000000 : ℝ)] ![(619050594811/20000000000000 : ℝ), (48342929532443/100000000000000 : ℝ), (6070227184519/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-324826143/5000000000 : ℝ)|^75 ≤ (619050594811/20000000000000 : ℝ)^59
        have hw : |(-324826143/5000000000 : ℝ)|=(324826143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5645147131/10000000000 : ℝ)|^75 ≤ (48342929532443/100000000000000 : ℝ)^59
        have hw : |(5645147131/10000000000 : ℝ)|=(5645147131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-566524479/1000000000 : ℝ)|^75 ≤ (6070227184519/12500000000000 : ℝ)^59
        have hw : |(-566524479/1000000000 : ℝ)|=(566524479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314060_s1_s1_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5960289939/10000000000 : ℝ)*x 0 + (-477821687/5000000000 : ℝ)*x 1 + (-5161955777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5960289939/10000000000 : ℝ)^75 ≤ (25899593832087/50000000000000 : ℝ)^59 := by
    have hnat : (5960289939 : ℕ)^75*50000000000000^59 ≤ 25899593832087^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5960289939 10000000000 25899593832087 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (477821687/5000000000 : ℝ)^75 ≤ (5055520953773/100000000000000 : ℝ)^59 := by
    have hnat : (477821687 : ℕ)^75*100000000000000^59 ≤ 5055520953773^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477821687 5000000000 5055520953773 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5161955777/10000000000 : ℝ)^75 ≤ (43145291371927/100000000000000 : ℝ)^59 := by
    have hnat : (5161955777 : ℕ)^75*100000000000000^59 ≤ 43145291371927^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161955777 10000000000 43145291371927 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5960289939/10000000000 : ℝ), (-477821687/5000000000 : ℝ), (-5161955777/10000000000 : ℝ)] ![(25899593832087/50000000000000 : ℝ), (5055520953773/100000000000000 : ℝ), (43145291371927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5960289939/10000000000 : ℝ)|^75 ≤ (25899593832087/50000000000000 : ℝ)^59
        have hw : |(5960289939/10000000000 : ℝ)|=(5960289939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-477821687/5000000000 : ℝ)|^75 ≤ (5055520953773/100000000000000 : ℝ)^59
        have hw : |(-477821687/5000000000 : ℝ)|=(477821687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5161955777/10000000000 : ℝ)|^75 ≤ (43145291371927/100000000000000 : ℝ)^59
        have hw : |(-5161955777/10000000000 : ℝ)|=(5161955777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314060_s1_s1_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (963452187/2500000000 : ℝ)*x 0 + (6725032673/10000000000 : ℝ)*x 1 + (25239579/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (963452187/2500000000 : ℝ)^75 ≤ (29757002686623/100000000000000 : ℝ)^59 := by
    have hnat : (963452187 : ℕ)^75*100000000000000^59 ≤ 29757002686623^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963452187 2500000000 29757002686623 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6725032673/10000000000 : ℝ)^75 ≤ (15097584347021/25000000000000 : ℝ)^59 := by
    have hnat : (6725032673 : ℕ)^75*25000000000000^59 ≤ 15097584347021^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6725032673 10000000000 15097584347021 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25239579/156250000 : ℝ)^75 ≤ (1970531981691/20000000000000 : ℝ)^59 := by
    have hnat : (25239579 : ℕ)^75*20000000000000^59 ≤ 1970531981691^59*156250000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25239579 156250000 1970531981691 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(963452187/2500000000 : ℝ), (6725032673/10000000000 : ℝ), (25239579/156250000 : ℝ)] ![(29757002686623/100000000000000 : ℝ), (15097584347021/25000000000000 : ℝ), (1970531981691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(963452187/2500000000 : ℝ)|^75 ≤ (29757002686623/100000000000000 : ℝ)^59
        have hw : |(963452187/2500000000 : ℝ)|=(963452187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6725032673/10000000000 : ℝ)|^75 ≤ (15097584347021/25000000000000 : ℝ)^59
        have hw : |(6725032673/10000000000 : ℝ)|=(6725032673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25239579/156250000 : ℝ)|^75 ≤ (1970531981691/20000000000000 : ℝ)^59
        have hw : |(25239579/156250000 : ℝ)|=(25239579/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314060_s1_s1_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4274094299/5000000000 : ℝ)*x 0 + (2572036937/10000000000 : ℝ)*x 1 + (-49200151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4274094299/5000000000 : ℝ)^75 ≤ (204804399877/250000000000 : ℝ)^59 := by
    have hnat : (4274094299 : ℕ)^75*250000000000^59 ≤ 204804399877^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274094299 5000000000 204804399877 250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2572036937/10000000000 : ℝ)^75 ≤ (17797228417417/100000000000000 : ℝ)^59 := by
    have hnat : (2572036937 : ℕ)^75*100000000000000^59 ≤ 17797228417417^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2572036937 10000000000 17797228417417 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49200151/5000000000 : ℝ)^75 ≤ (11240464761/4000000000000 : ℝ)^59 := by
    have hnat : (49200151 : ℕ)^75*4000000000000^59 ≤ 11240464761^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49200151 5000000000 11240464761 4000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4274094299/5000000000 : ℝ), (2572036937/10000000000 : ℝ), (-49200151/5000000000 : ℝ)] ![(204804399877/250000000000 : ℝ), (17797228417417/100000000000000 : ℝ), (11240464761/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4274094299/5000000000 : ℝ)|^75 ≤ (204804399877/250000000000 : ℝ)^59
        have hw : |(4274094299/5000000000 : ℝ)|=(4274094299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2572036937/10000000000 : ℝ)|^75 ≤ (17797228417417/100000000000000 : ℝ)^59
        have hw : |(2572036937/10000000000 : ℝ)|=(2572036937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49200151/5000000000 : ℝ)|^75 ≤ (11240464761/4000000000000 : ℝ)^59
        have hw : |(-49200151/5000000000 : ℝ)|=(49200151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314060_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((82361/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(82361/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(81997/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(81997/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2289/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2289/3125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((57661/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(57661/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1203/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1203/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8961/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8961/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (87867/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s1_pow0 : (82361/100000 : ℝ) ^ (37/8 : ℝ) ≤ (20378980576866990131/50000000000000000000 : ℝ) := by
    have hpowers : (82361/100000 : ℝ)^37 ≤ (20378980576866990131/50000000000000000000 : ℝ)^8 := by
      have hnat : (82361 : ℕ)^37*50000000000000000000^8 ≤ 20378980576866990131^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82361 100000 20378980576866990131 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (82361/100000 : ℝ)) (X := (20378980576866990131/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (70378980576866990131/50000000000000000000 : ℝ) ≤ (269179679643419/250000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (70378980576866990131/50000000000000000000 : ℝ)^8 ≤ (269179679643419/250000000000000 : ℝ)^37 := by
      have hnat : (70378980576866990131 : ℕ)^8*250000000000000^37 ≤ 269179679643419^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70378980576866990131 50000000000000000000 269179679643419 250000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (269179679643419/250000000000000 : ℝ)) (X := (70378980576866990131/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (45378980576866990131/25000000000000000000 : ℝ) ≤ (177746717219251/156250000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (45378980576866990131/25000000000000000000 : ℝ)^8 ≤ (177746717219251/156250000000000 : ℝ)^37 := by
      have hnat : (45378980576866990131 : ℕ)^8*156250000000000^37 ≤ 177746717219251^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45378980576866990131 25000000000000000000 177746717219251 156250000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (177746717219251/156250000000000 : ℝ)) (X := (45378980576866990131/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(19179679643419/205902500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(76075339536913/1029512500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (82361/100000 : ℝ)) (alpha := (19179679643419/205902500000000 : ℝ)) (beta := (76075339536913/1029512500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (82361/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(19179679643419/205902500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(76075339536913/1029512500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (81997/100000 : ℝ) ^ (37/8 : ℝ) ≤ (7986299184345922913/20000000000000000000 : ℝ) := by
    have hpowers : (81997/100000 : ℝ)^37 ≤ (7986299184345922913/20000000000000000000 : ℝ)^8 := by
      have hnat : (81997 : ℕ)^37*20000000000000000000^8 ≤ 7986299184345922913^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81997 100000 7986299184345922913 20000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (81997/100000 : ℝ)) (X := (7986299184345922913/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (27986299184345922913/20000000000000000000 : ℝ) ≤ (2150697290511669/2000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (27986299184345922913/20000000000000000000 : ℝ)^8 ≤ (2150697290511669/2000000000000000 : ℝ)^37 := by
      have hnat : (27986299184345922913 : ℕ)^8*2000000000000000^37 ≤ 2150697290511669^37*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27986299184345922913 20000000000000000000 2150697290511669 2000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2150697290511669/2000000000000000 : ℝ)) (X := (27986299184345922913/20000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (17986299184345922913/10000000000000000000 : ℝ) ≤ (5676655756280891/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (17986299184345922913/10000000000000000000 : ℝ)^8 ≤ (5676655756280891/5000000000000000 : ℝ)^37 := by
      have hnat : (17986299184345922913 : ℕ)^8*5000000000000000^37 ≤ 5676655756280891^37*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17986299184345922913 10000000000000000000 5676655756280891 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5676655756280891/5000000000000000 : ℝ)) (X := (17986299184345922913/10000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(150697290511669/1639940000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(599825060003437/8199700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (81997/100000 : ℝ)) (alpha := (150697290511669/1639940000000000 : ℝ)) (beta := (599825060003437/8199700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (81997/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(150697290511669/1639940000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(599825060003437/8199700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (2289/3125 : ℝ) ^ (37/8 : ℝ) ≤ (5924073654762513619/25000000000000000000 : ℝ) := by
    have hpowers : (2289/3125 : ℝ)^37 ≤ (5924073654762513619/25000000000000000000 : ℝ)^8 := by
      have hnat : (2289 : ℕ)^37*25000000000000000000^8 ≤ 5924073654762513619^8*3125^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2289 3125 5924073654762513619 25000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2289/3125 : ℝ)) (X := (5924073654762513619/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (30924073654762513619/25000000000000000000 : ℝ) ≤ (10470538405924227/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (30924073654762513619/25000000000000000000 : ℝ)^8 ≤ (10470538405924227/10000000000000000 : ℝ)^37 := by
      have hnat : (30924073654762513619 : ℕ)^8*10000000000000000^37 ≤ 10470538405924227^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30924073654762513619 25000000000000000000 10470538405924227 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10470538405924227/10000000000000000 : ℝ)) (X := (30924073654762513619/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (18424073654762513619/12500000000000000000 : ℝ) ≤ (10874947453427581/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (18424073654762513619/12500000000000000000 : ℝ)^8 ≤ (10874947453427581/10000000000000000 : ℝ)^37 := by
      have hnat : (18424073654762513619 : ℕ)^8*10000000000000000^37 ≤ 10874947453427581^37*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18424073654762513619 12500000000000000000 10874947453427581 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10874947453427581/10000000000000000 : ℝ)) (X := (18424073654762513619/12500000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(470538405924227/7324800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(202204523751677/3662400000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (2289/3125 : ℝ)) (alpha := (470538405924227/7324800000000000 : ℝ)) (beta := (202204523751677/3662400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (2289/3125 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(470538405924227/7324800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(202204523751677/3662400000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-365092769/2000000000 : ℝ)*X 0 0+(2129707083/5000000000 : ℝ)*X 0 1+(-3110513489/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314060_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((898461641/2000000000 : ℝ)*X 1 0+(-1024805359/5000000000 : ℝ)*X 1 1+(-2921412231/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314060_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1171172801/2500000000 : ℝ)*X 2 0+(1493418881/2500000000 : ℝ)*X 2 1+(1623170419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314060_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1867239563/10000000000 : ℝ)*X 0 0+(3449159289/10000000000 : ℝ)*X 0 1+(-1378546161/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314060_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((952781241/2500000000 : ℝ)*X 1 0+(-713336951/5000000000 : ℝ)*X 1 1+(-6887205531/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314060_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4016930171/10000000000 : ℝ)*X 2 0+(6916941679/10000000000 : ℝ)*X 2 1+(1099696573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314060_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((89632053/156250000 : ℝ)*X 0 0+(1171122153/2000000000 : ℝ)*X 0 1+(-2512061/2500000000 : ℝ)*X 0 2+(89632053/156250000 : ℝ)*X 1 0+(1171122153/2000000000 : ℝ)*X 1 1+(-2512061/2500000000 : ℝ)*X 1 2+(89632053/156250000 : ℝ)*X 2 0+(1171122153/2000000000 : ℝ)*X 2 1+(-2512061/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314060_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1127438581/10000000000 : ℝ)*X 0 0+(46624559/125000000 : ℝ)*X 0 1+(-714423149/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314060_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1640901771/5000000000 : ℝ)*X 1 0+(-854929867/5000000000 : ℝ)*X 1 1+(-7138490069/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314060_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3053026033/5000000000 : ℝ)*X 2 0+(4876792341/10000000000 : ℝ)*X 2 1+(144629959/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314060_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((4023848717/5000000000 : ℝ)*X 0 0+(130403019/400000000 : ℝ)*X 0 1+(-4141617/1250000000 : ℝ)*X 0 2+(4023848717/5000000000 : ℝ)*X 1 0+(130403019/400000000 : ℝ)*X 1 1+(-4141617/1250000000 : ℝ)*X 1 2+(4023848717/5000000000 : ℝ)*X 2 0+(130403019/400000000 : ℝ)*X 2 1+(-4141617/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314060_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-324826143/5000000000 : ℝ)*X 0 0+(5645147131/10000000000 : ℝ)*X 0 1+(-566524479/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314060_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5960289939/10000000000 : ℝ)*X 1 0+(-477821687/5000000000 : ℝ)*X 1 1+(-5161955777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314060_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((963452187/2500000000 : ℝ)*X 2 0+(6725032673/10000000000 : ℝ)*X 2 1+(25239579/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314060_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((4274094299/5000000000 : ℝ)*X 0 0+(2572036937/10000000000 : ℝ)*X 0 1+(-49200151/5000000000 : ℝ)*X 0 2+(4274094299/5000000000 : ℝ)*X 1 0+(2572036937/10000000000 : ℝ)*X 1 1+(-49200151/5000000000 : ℝ)*X 1 2+(4274094299/5000000000 : ℝ)*X 2 0+(2572036937/10000000000 : ℝ)*X 2 1+(-49200151/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314060_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((57661/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(57661/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1748163593106866539665117266793/329779827306944000000000000000000000 : ℝ) := by norm_num
    linear_combination (127497231891/250000000000 : ℝ)*(base7) + (3007/10000000000 : ℝ)*(base39) + (65422324157/250000000000 : ℝ)*(base59) + (3972765479793/1000000000000 : ℝ)*(major_s1_0) + (3972765479793/1000000000000 : ℝ)*(major_s1_1) + (3972765479793/1000000000000 : ℝ)*(major_s1_2) + (1824119/500000000000 : ℝ)*(sp_s1_0) + (255363/50000000000 : ℝ)*(sp_s1_1) + (5337942500369/1000000000000 : ℝ)*(sp_s1_7) + (5337950291941/1000000000000 : ℝ)*(sp_s1_8) + (5337966719757/1000000000000 : ℝ)*(sp_s1_9) + (2818810086397/1000000000000 : ℝ)*(sp_s1_13) + (20571151/1000000000000 : ℝ)*(sp_s1_14) + (2830139/250000000000 : ℝ)*(sp_s1_15) + (2308821158833/1000000000000 : ℝ)*(f.failure) + (5337966719757/1000000000000 : ℝ)*(f.sum) + (69644663395147793629/200203875200000000000000000000000 : ℝ)*base63 + (316003418368207/1220800000000000000000000000 : ℝ)*base64 + (5341592094578531/8199700000000000000000000000 : ℝ)*base67 + (419260697764337/2441600000000000000000000000 : ℝ)*base69 + (14615916106662597513/100546308800000000000000000000000 : ℝ)*base71 + (1373102070057449/4118050000000000000000000000 : ℝ)*base72 + (334925782578943/1639940000000000000000000000 : ℝ)*base75 + (2213956983781/10295125000000000000000000 : ℝ)*base77 + (7282168856951093829/27013419668000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (64523/100000000000000000 : ℝ)*base86 + (64523/100000000000000000 : ℝ)*base88 + (64523/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1203/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1203/2000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (56038736603821458878094022272523/4122247841336800000000000000000000000 : ℝ) := by norm_num
    linear_combination (632822034461/1000000000000 : ℝ)*(base7) + (2779139/1000000000000 : ℝ)*(base39) + (1512389/1000000000000 : ℝ)*(base59) + (1480592999497/500000000000 : ℝ)*(major_s1_0) + (1480592999497/500000000000 : ℝ)*(major_s1_1) + (1480592999497/500000000000 : ℝ)*(major_s1_2) + (10901587/1000000000000 : ℝ)*(sp_s1_0) + (33371677/1000000000000 : ℝ)*(sp_s1_2) + (563257/31250000000 : ℝ)*(sp_s1_7) + (1686567/12500000000 : ℝ)*(sp_s1_8) + (957678663849/250000000000 : ℝ)*(sp_s1_14) + (3830608655847/1000000000000 : ℝ)*(sp_s1_15) + (383071020953/100000000000 : ℝ)*(sp_s1_16) + (2353751428479/1000000000000 : ℝ)*(sp_s1_20) + (860464697009/500000000000 : ℝ)*(f.failure) + (3830743581207/1000000000000 : ℝ)*(f.sum) + (66165970184869518623/300305812800000000000000000000000 : ℝ)*base63 + (1570322072905771/1831200000000000000000000000 : ℝ)*base65 + (1702099175910661/4099850000000000000000000000 : ℝ)*base66 + (2556146722313819/3662400000000000000000000000 : ℝ)*base69 + (65159910257994075731/150819463200000000000000000000000 : ℝ)*base71 + (2387548706493577/4118050000000000000000000000 : ℝ)*base72 + (103868688057083/163994000000000000000000000 : ℝ)*base75 + (526186052678861/823610000000000000000000000 : ℝ)*base77 + (78212457646843277/1350670983400000000000000000000 : ℝ)*base78 + (58379/50000000000000000 : ℝ)*base86 + (58379/50000000000000000 : ℝ)*base88 + (58379/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8961/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8961/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (164926557281277222201196179/20109261760000000000000000000000 : ℝ) := by norm_num
    linear_combination (242221931453/1000000000000 : ℝ)*(base7) + (9530949/1000000000000 : ℝ)*(base11) + (215738986719/1000000000000 : ℝ)*(base39) + (1088683/1000000000000 : ℝ)*(base43) + (3154060095519/1000000000000 : ℝ)*(major_s1_0) + (788514751709/250000000000 : ℝ)*(major_s1_1) + (3154060095519/1000000000000 : ℝ)*(major_s1_2) + (21940299/1000000000000 : ℝ)*(sp_s1_0) + (79542929/1000000000000 : ℝ)*(sp_s1_9) + (429261/250000000000 : ℝ)*(sp_s1_20) + (10832939011/2500000000 : ℝ)*(sp_s1_21) + (433320816433/100000000000 : ℝ)*(sp_s1_22) + (2166563766359/500000000000 : ℝ)*(sp_s1_23) + (1037620372133/500000000000 : ℝ)*(sp_s1_27) + (1833020529857/1000000000000 : ℝ)*(f.failure) + (433320816433/100000000000 : ℝ)*(f.sum) + (32203446572435985773/200203875200000000000000000000000 : ℝ)*base62 + (1172796471711201/1220800000000000000000000000 : ℝ)*base64 + (46994393487149/1024962500000000000000000000 : ℝ)*base67 + (262076488755169/2441600000000000000000000000 : ℝ)*base68 + (4897573990159330521/100546308800000000000000000000000 : ℝ)*base70 + (653737122441091/2059025000000000000000000000 : ℝ)*base72 + (26251460366903/819970000000000000000000000 : ℝ)*base75 + (133341935851223/823610000000000000000000000 : ℝ)*base76 + (82172125030799065003/337667745850000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (64133/100000000000000000 : ℝ)*base87 + (64133/100000000000000000 : ℝ)*base89 + (64133/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((82361/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(82361/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(81997/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(81997/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2289/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2289/3125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((57661/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(57661/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1203/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1203/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8961/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8961/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314060_s1 p hpa hpb X hX hprev0

#print axioms solution

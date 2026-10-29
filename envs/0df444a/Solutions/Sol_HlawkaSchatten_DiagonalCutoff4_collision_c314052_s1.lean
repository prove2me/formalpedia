-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314052_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:46:13.160981+00:00
-- url     : https://prove2.me/submissions/ac04e23c-1b42-46a5-b5c9-da9493a49f76

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
theorem collision_support_c314052_s1_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1835340057/10000000000 : ℝ)*x 0 + (1744408707/5000000000 : ℝ)*x 1 + (-1370854509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1835340057/10000000000 : ℝ)^19 ≤ (2335631285351/20000000000000 : ℝ)^15 := by
    have hnat : (1835340057 : ℕ)^19*20000000000000^15 ≤ 2335631285351^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1835340057 10000000000 2335631285351 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1744408707/5000000000 : ℝ)^19 ≤ (5269334492983/20000000000000 : ℝ)^15 := by
    have hnat : (1744408707 : ℕ)^19*20000000000000^15 ≤ 5269334492983^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744408707 5000000000 5269334492983 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370854509/2000000000 : ℝ)^19 ≤ (61975171083227/100000000000000 : ℝ)^15 := by
    have hnat : (1370854509 : ℕ)^19*100000000000000^15 ≤ 61975171083227^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370854509 2000000000 61975171083227 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1835340057/10000000000 : ℝ), (1744408707/5000000000 : ℝ), (-1370854509/2000000000 : ℝ)] ![(2335631285351/20000000000000 : ℝ), (5269334492983/20000000000000 : ℝ), (61975171083227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1835340057/10000000000 : ℝ)|^19 ≤ (2335631285351/20000000000000 : ℝ)^15
        have hw : |(-1835340057/10000000000 : ℝ)|=(1835340057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1744408707/5000000000 : ℝ)|^19 ≤ (5269334492983/20000000000000 : ℝ)^15
        have hw : |(1744408707/5000000000 : ℝ)|=(1744408707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1370854509/2000000000 : ℝ)|^19 ≤ (61975171083227/100000000000000 : ℝ)^15
        have hw : |(-1370854509/2000000000 : ℝ)|=(1370854509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314052_s1_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4845431183/10000000000 : ℝ)*x 0 + (1158208703/2000000000 : ℝ)*x 1 + (811803231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4845431183/10000000000 : ℝ)^19 ≤ (39941197161181/100000000000000 : ℝ)^15 := by
    have hnat : (4845431183 : ℕ)^19*100000000000000^15 ≤ 39941197161181^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4845431183 10000000000 39941197161181 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1158208703/2000000000 : ℝ)^19 ≤ (50060131089463/100000000000000 : ℝ)^15 := by
    have hnat : (1158208703 : ℕ)^19*100000000000000^15 ≤ 50060131089463^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158208703 2000000000 50060131089463 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (811803231/5000000000 : ℝ)^19 ≤ (4999335864907/50000000000000 : ℝ)^15 := by
    have hnat : (811803231 : ℕ)^19*50000000000000^15 ≤ 4999335864907^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811803231 5000000000 4999335864907 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4845431183/10000000000 : ℝ), (1158208703/2000000000 : ℝ), (811803231/5000000000 : ℝ)] ![(39941197161181/100000000000000 : ℝ), (50060131089463/100000000000000 : ℝ), (4999335864907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4845431183/10000000000 : ℝ)|^19 ≤ (39941197161181/100000000000000 : ℝ)^15
        have hw : |(4845431183/10000000000 : ℝ)|=(4845431183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1158208703/2000000000 : ℝ)|^19 ≤ (50060131089463/100000000000000 : ℝ)^15
        have hw : |(1158208703/2000000000 : ℝ)|=(1158208703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(811803231/5000000000 : ℝ)|^19 ≤ (4999335864907/50000000000000 : ℝ)^15
        have hw : |(811803231/5000000000 : ℝ)|=(811803231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314052_s1_s1_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6564823071/10000000000 : ℝ)*x 0 + (4172665633/10000000000 : ℝ)*x 1 + (-1397595521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6564823071/10000000000 : ℝ)^19 ≤ (58678972356883/100000000000000 : ℝ)^15 := by
    have hnat : (6564823071 : ℕ)^19*100000000000000^15 ≤ 58678972356883^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6564823071 10000000000 58678972356883 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4172665633/10000000000 : ℝ)^19 ≤ (33051451805091/100000000000000 : ℝ)^15 := by
    have hnat : (4172665633 : ℕ)^19*100000000000000^15 ≤ 33051451805091^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172665633 10000000000 33051451805091 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1397595521/10000000000 : ℝ)^19 ≤ (2067393955601/25000000000000 : ℝ)^15 := by
    have hnat : (1397595521 : ℕ)^19*25000000000000^15 ≤ 2067393955601^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397595521 10000000000 2067393955601 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6564823071/10000000000 : ℝ), (4172665633/10000000000 : ℝ), (-1397595521/10000000000 : ℝ)] ![(58678972356883/100000000000000 : ℝ), (33051451805091/100000000000000 : ℝ), (2067393955601/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6564823071/10000000000 : ℝ)|^19 ≤ (58678972356883/100000000000000 : ℝ)^15
        have hw : |(6564823071/10000000000 : ℝ)|=(6564823071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4172665633/10000000000 : ℝ)|^19 ≤ (33051451805091/100000000000000 : ℝ)^15
        have hw : |(4172665633/10000000000 : ℝ)|=(4172665633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1397595521/10000000000 : ℝ)|^19 ≤ (2067393955601/25000000000000 : ℝ)^15
        have hw : |(-1397595521/10000000000 : ℝ)|=(1397595521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314052_s1_s1_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-812226529/5000000000 : ℝ)*x 0 + (721470193/2500000000 : ℝ)*x 1 + (-3742111937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (812226529/5000000000 : ℝ)^19 ≤ (5002638041437/50000000000000 : ℝ)^15 := by
    have hnat : (812226529 : ℕ)^19*50000000000000^15 ≤ 5002638041437^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      812226529 5000000000 5002638041437 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (721470193/2500000000 : ℝ)^19 ≤ (1294889286913/6250000000000 : ℝ)^15 := by
    have hnat : (721470193 : ℕ)^19*6250000000000^15 ≤ 1294889286913^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721470193 2500000000 1294889286913 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3742111937/5000000000 : ℝ)^19 ≤ (8659561913467/12500000000000 : ℝ)^15 := by
    have hnat : (3742111937 : ℕ)^19*12500000000000^15 ≤ 8659561913467^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3742111937 5000000000 8659561913467 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-812226529/5000000000 : ℝ), (721470193/2500000000 : ℝ), (-3742111937/5000000000 : ℝ)] ![(5002638041437/50000000000000 : ℝ), (1294889286913/6250000000000 : ℝ), (8659561913467/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-812226529/5000000000 : ℝ)|^19 ≤ (5002638041437/50000000000000 : ℝ)^15
        have hw : |(-812226529/5000000000 : ℝ)|=(812226529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(721470193/2500000000 : ℝ)|^19 ≤ (1294889286913/6250000000000 : ℝ)^15
        have hw : |(721470193/2500000000 : ℝ)|=(721470193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3742111937/5000000000 : ℝ)|^19 ≤ (8659561913467/12500000000000 : ℝ)^15
        have hw : |(-3742111937/5000000000 : ℝ)|=(3742111937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314052_s1_s1_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1070726909/2500000000 : ℝ)*x 0 + (-2254851809/10000000000 : ℝ)*x 1 + (-1461929397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070726909/2500000000 : ℝ)^19 ≤ (34161402909047/100000000000000 : ℝ)^15 := by
    have hnat : (1070726909 : ℕ)^19*100000000000000^15 ≤ 34161402909047^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070726909 2500000000 34161402909047 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254851809/10000000000 : ℝ)^19 ≤ (189463760313/1250000000000 : ℝ)^15 := by
    have hnat : (2254851809 : ℕ)^19*1250000000000^15 ≤ 189463760313^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254851809 10000000000 189463760313 1250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1461929397/2500000000 : ℝ)^19 ≤ (25340748125957/50000000000000 : ℝ)^15 := by
    have hnat : (1461929397 : ℕ)^19*50000000000000^15 ≤ 25340748125957^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461929397 2500000000 25340748125957 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070726909/2500000000 : ℝ), (-2254851809/10000000000 : ℝ), (-1461929397/2500000000 : ℝ)] ![(34161402909047/100000000000000 : ℝ), (189463760313/1250000000000 : ℝ), (25340748125957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070726909/2500000000 : ℝ)|^19 ≤ (34161402909047/100000000000000 : ℝ)^15
        have hw : |(1070726909/2500000000 : ℝ)|=(1070726909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2254851809/10000000000 : ℝ)|^19 ≤ (189463760313/1250000000000 : ℝ)^15
        have hw : |(-2254851809/10000000000 : ℝ)|=(2254851809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1461929397/2500000000 : ℝ)|^19 ≤ (25340748125957/50000000000000 : ℝ)^15
        have hw : |(-1461929397/2500000000 : ℝ)|=(1461929397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314052_s1_s1_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2255303973/5000000000 : ℝ)*x 0 + (3377026411/5000000000 : ℝ)*x 1 + (144070611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2255303973/5000000000 : ℝ)^19 ≤ (36478006983229/100000000000000 : ℝ)^15 := by
    have hnat : (2255303973 : ℕ)^19*100000000000000^15 ≤ 36478006983229^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255303973 5000000000 36478006983229 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3377026411/5000000000 : ℝ)^19 ≤ (15207400452801/25000000000000 : ℝ)^15 := by
    have hnat : (3377026411 : ℕ)^19*25000000000000^15 ≤ 15207400452801^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3377026411 5000000000 15207400452801 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (144070611/2500000000 : ℝ)^19 ≤ (336548897999/12500000000000 : ℝ)^15 := by
    have hnat : (144070611 : ℕ)^19*12500000000000^15 ≤ 336548897999^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144070611 2500000000 336548897999 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2255303973/5000000000 : ℝ), (3377026411/5000000000 : ℝ), (144070611/2500000000 : ℝ)] ![(36478006983229/100000000000000 : ℝ), (15207400452801/25000000000000 : ℝ), (336548897999/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2255303973/5000000000 : ℝ)|^19 ≤ (36478006983229/100000000000000 : ℝ)^15
        have hw : |(2255303973/5000000000 : ℝ)|=(2255303973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3377026411/5000000000 : ℝ)|^19 ≤ (15207400452801/25000000000000 : ℝ)^15
        have hw : |(3377026411/5000000000 : ℝ)|=(3377026411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(144070611/2500000000 : ℝ)|^19 ≤ (336548897999/12500000000000 : ℝ)^15
        have hw : |(144070611/2500000000 : ℝ)|=(144070611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314052_s1_s1_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6007765323/10000000000 : ℝ)*x 0 + (1074821719/2000000000 : ℝ)*x 1 + (-114635039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6007765323/10000000000 : ℝ)^19 ≤ (52444878354721/100000000000000 : ℝ)^15 := by
    have hnat : (6007765323 : ℕ)^19*100000000000000^15 ≤ 52444878354721^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6007765323 10000000000 52444878354721 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1074821719/2000000000 : ℝ)^19 ≤ (22769744590833/50000000000000 : ℝ)^15 := by
    have hnat : (1074821719 : ℕ)^19*50000000000000^15 ≤ 22769744590833^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074821719 2000000000 22769744590833 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114635039/2500000000 : ℝ)^19 ≤ (503908111777/25000000000000 : ℝ)^15 := by
    have hnat : (114635039 : ℕ)^19*25000000000000^15 ≤ 503908111777^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114635039 2500000000 503908111777 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6007765323/10000000000 : ℝ), (1074821719/2000000000 : ℝ), (-114635039/2500000000 : ℝ)] ![(52444878354721/100000000000000 : ℝ), (22769744590833/50000000000000 : ℝ), (503908111777/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6007765323/10000000000 : ℝ)|^19 ≤ (52444878354721/100000000000000 : ℝ)^15
        have hw : |(6007765323/10000000000 : ℝ)|=(6007765323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1074821719/2000000000 : ℝ)|^19 ≤ (22769744590833/50000000000000 : ℝ)^15
        have hw : |(1074821719/2000000000 : ℝ)|=(1074821719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-114635039/2500000000 : ℝ)|^19 ≤ (503908111777/25000000000000 : ℝ)^15
        have hw : |(-114635039/2500000000 : ℝ)|=(114635039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314052_s1_s1_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-892456597/10000000000 : ℝ)*x 0 + (3352548253/10000000000 : ℝ)*x 1 + (-3784186581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892456597/10000000000 : ℝ)^19 ≤ (36604433977/781250000000 : ℝ)^15 := by
    have hnat : (892456597 : ℕ)^19*781250000000^15 ≤ 36604433977^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892456597 10000000000 36604433977 781250000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3352548253/10000000000 : ℝ)^19 ≤ (50100075033/200000000000 : ℝ)^15 := by
    have hnat : (3352548253 : ℕ)^19*200000000000^15 ≤ 50100075033^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3352548253 10000000000 50100075033 200000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3784186581/5000000000 : ℝ)^19 ≤ (17566148730181/25000000000000 : ℝ)^15 := by
    have hnat : (3784186581 : ℕ)^19*25000000000000^15 ≤ 17566148730181^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3784186581 5000000000 17566148730181 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-892456597/10000000000 : ℝ), (3352548253/10000000000 : ℝ), (-3784186581/5000000000 : ℝ)] ![(36604433977/781250000000 : ℝ), (50100075033/200000000000 : ℝ), (17566148730181/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-892456597/10000000000 : ℝ)|^19 ≤ (36604433977/781250000000 : ℝ)^15
        have hw : |(-892456597/10000000000 : ℝ)|=(892456597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3352548253/10000000000 : ℝ)|^19 ≤ (50100075033/200000000000 : ℝ)^15
        have hw : |(3352548253/10000000000 : ℝ)|=(3352548253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3784186581/5000000000 : ℝ)|^19 ≤ (17566148730181/25000000000000 : ℝ)^15
        have hw : |(-3784186581/5000000000 : ℝ)|=(3784186581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314052_s1_s1_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2113243577/5000000000 : ℝ)*x 0 + (-2520424707/10000000000 : ℝ)*x 1 + (-5689855377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113243577/5000000000 : ℝ)^19 ≤ (16796189733141/50000000000000 : ℝ)^15 := by
    have hnat : (2113243577 : ℕ)^19*50000000000000^15 ≤ 16796189733141^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113243577 5000000000 16796189733141 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2520424707/10000000000 : ℝ)^19 ≤ (436321618011/2500000000000 : ℝ)^15 := by
    have hnat : (2520424707 : ℕ)^19*2500000000000^15 ≤ 436321618011^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2520424707 10000000000 436321618011 2500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5689855377/10000000000 : ℝ)^19 ≤ (611934447477/1250000000000 : ℝ)^15 := by
    have hnat : (5689855377 : ℕ)^19*1250000000000^15 ≤ 611934447477^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5689855377 10000000000 611934447477 1250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2113243577/5000000000 : ℝ), (-2520424707/10000000000 : ℝ), (-5689855377/10000000000 : ℝ)] ![(16796189733141/50000000000000 : ℝ), (436321618011/2500000000000 : ℝ), (611934447477/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2113243577/5000000000 : ℝ)|^19 ≤ (16796189733141/50000000000000 : ℝ)^15
        have hw : |(2113243577/5000000000 : ℝ)|=(2113243577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2520424707/10000000000 : ℝ)|^19 ≤ (436321618011/2500000000000 : ℝ)^15
        have hw : |(-2520424707/10000000000 : ℝ)|=(2520424707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5689855377/10000000000 : ℝ)|^19 ≤ (611934447477/1250000000000 : ℝ)^15
        have hw : |(-5689855377/10000000000 : ℝ)|=(5689855377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314052_s1_s1_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (234049571/400000000 : ℝ)*x 0 + (5424667687/10000000000 : ℝ)*x 1 + (329991509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (234049571/400000000 : ℝ)^19 ≤ (50720160627407/100000000000000 : ℝ)^15 := by
    have hnat : (234049571 : ℕ)^19*100000000000000^15 ≤ 50720160627407^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234049571 400000000 50720160627407 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424667687/10000000000 : ℝ)^19 ≤ (144008899181/312500000000 : ℝ)^15 := by
    have hnat : (5424667687 : ℕ)^19*312500000000^15 ≤ 144008899181^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424667687 10000000000 144008899181 312500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329991509/5000000000 : ℝ)^19 ≤ (3196991614163/100000000000000 : ℝ)^15 := by
    have hnat : (329991509 : ℕ)^19*100000000000000^15 ≤ 3196991614163^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329991509 5000000000 3196991614163 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(234049571/400000000 : ℝ), (5424667687/10000000000 : ℝ), (329991509/5000000000 : ℝ)] ![(50720160627407/100000000000000 : ℝ), (144008899181/312500000000 : ℝ), (3196991614163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(234049571/400000000 : ℝ)|^19 ≤ (50720160627407/100000000000000 : ℝ)^15
        have hw : |(234049571/400000000 : ℝ)|=(234049571/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424667687/10000000000 : ℝ)|^19 ≤ (144008899181/312500000000 : ℝ)^15
        have hw : |(5424667687/10000000000 : ℝ)|=(5424667687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329991509/5000000000 : ℝ)|^19 ≤ (3196991614163/100000000000000 : ℝ)^15
        have hw : |(329991509/5000000000 : ℝ)|=(329991509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314052_s1_s1_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7631417937/10000000000 : ℝ)*x 0 + (892153469/2500000000 : ℝ)*x 1 + (-434169371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7631417937/10000000000 : ℝ)^19 ≤ (71006804514571/100000000000000 : ℝ)^15 := by
    have hnat : (7631417937 : ℕ)^19*100000000000000^15 ≤ 71006804514571^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7631417937 10000000000 71006804514571 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (892153469/2500000000 : ℝ)^19 ≤ (27112284253351/100000000000000 : ℝ)^15 := by
    have hnat : (892153469 : ℕ)^19*100000000000000^15 ≤ 27112284253351^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892153469 2500000000 27112284253351 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434169371/10000000000 : ℝ)^19 ≤ (940455611227/50000000000000 : ℝ)^15 := by
    have hnat : (434169371 : ℕ)^19*50000000000000^15 ≤ 940455611227^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434169371 10000000000 940455611227 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7631417937/10000000000 : ℝ), (892153469/2500000000 : ℝ), (-434169371/10000000000 : ℝ)] ![(71006804514571/100000000000000 : ℝ), (27112284253351/100000000000000 : ℝ), (940455611227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7631417937/10000000000 : ℝ)|^19 ≤ (71006804514571/100000000000000 : ℝ)^15
        have hw : |(7631417937/10000000000 : ℝ)|=(7631417937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(892153469/2500000000 : ℝ)|^19 ≤ (27112284253351/100000000000000 : ℝ)^15
        have hw : |(892153469/2500000000 : ℝ)|=(892153469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434169371/10000000000 : ℝ)|^19 ≤ (940455611227/50000000000000 : ℝ)^15
        have hw : |(-434169371/10000000000 : ℝ)|=(434169371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314052_s1_s1_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-107986881/2000000000 : ℝ)*x 0 + (52062911/125000000 : ℝ)*x 1 + (-3538887557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107986881/2000000000 : ℝ)^19 ≤ (619781503341/25000000000000 : ℝ)^15 := by
    have hnat : (107986881 : ℕ)^19*25000000000000^15 ≤ 619781503341^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107986881 2000000000 619781503341 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52062911/125000000 : ℝ)^19 ≤ (32974889584159/100000000000000 : ℝ)^15 := by
    have hnat : (52062911 : ℕ)^19*100000000000000^15 ≤ 32974889584159^15*125000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52062911 125000000 32974889584159 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3538887557/5000000000 : ℝ)^19 ≤ (1008531006147/1562500000000 : ℝ)^15 := by
    have hnat : (3538887557 : ℕ)^19*1562500000000^15 ≤ 1008531006147^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3538887557 5000000000 1008531006147 1562500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107986881/2000000000 : ℝ), (52062911/125000000 : ℝ), (-3538887557/5000000000 : ℝ)] ![(619781503341/25000000000000 : ℝ), (32974889584159/100000000000000 : ℝ), (1008531006147/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107986881/2000000000 : ℝ)|^19 ≤ (619781503341/25000000000000 : ℝ)^15
        have hw : |(-107986881/2000000000 : ℝ)|=(107986881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52062911/125000000 : ℝ)|^19 ≤ (32974889584159/100000000000000 : ℝ)^15
        have hw : |(52062911/125000000 : ℝ)|=(52062911/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3538887557/5000000000 : ℝ)|^19 ≤ (1008531006147/1562500000000 : ℝ)^15
        have hw : |(-3538887557/5000000000 : ℝ)|=(3538887557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314052_s1_s1_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5976060549/10000000000 : ℝ)*x 0 + (-1188140753/5000000000 : ℝ)*x 1 + (-4038092037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5976060549/10000000000 : ℝ)^19 ≤ (52094553430763/100000000000000 : ℝ)^15 := by
    have hnat : (5976060549 : ℕ)^19*100000000000000^15 ≤ 52094553430763^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5976060549 10000000000 52094553430763 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1188140753/5000000000 : ℝ)^19 ≤ (16198345507959/100000000000000 : ℝ)^15 := by
    have hnat : (1188140753 : ℕ)^19*100000000000000^15 ≤ 16198345507959^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188140753 5000000000 16198345507959 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4038092037/10000000000 : ℝ)^19 ≤ (1981693815933/6250000000000 : ℝ)^15 := by
    have hnat : (4038092037 : ℕ)^19*6250000000000^15 ≤ 1981693815933^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038092037 10000000000 1981693815933 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5976060549/10000000000 : ℝ), (-1188140753/5000000000 : ℝ), (-4038092037/10000000000 : ℝ)] ![(52094553430763/100000000000000 : ℝ), (16198345507959/100000000000000 : ℝ), (1981693815933/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5976060549/10000000000 : ℝ)|^19 ≤ (52094553430763/100000000000000 : ℝ)^15
        have hw : |(5976060549/10000000000 : ℝ)|=(5976060549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1188140753/5000000000 : ℝ)|^19 ≤ (16198345507959/100000000000000 : ℝ)^15
        have hw : |(-1188140753/5000000000 : ℝ)|=(1188140753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4038092037/10000000000 : ℝ)|^19 ≤ (1981693815933/6250000000000 : ℝ)^15
        have hw : |(-4038092037/10000000000 : ℝ)|=(4038092037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314052_s1_s1_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (428572793/1000000000 : ℝ)*x 0 + (6373164801/10000000000 : ℝ)*x 1 + (153239367/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428572793/1000000000 : ℝ)^19 ≤ (8547474857433/25000000000000 : ℝ)^15 := by
    have hnat : (428572793 : ℕ)^19*25000000000000^15 ≤ 8547474857433^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428572793 1000000000 8547474857433 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6373164801/10000000000 : ℝ)^19 ≤ (11303506391773/20000000000000 : ℝ)^15 := by
    have hnat : (6373164801 : ℕ)^19*20000000000000^15 ≤ 11303506391773^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6373164801 10000000000 11303506391773 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153239367/1000000000 : ℝ)^19 ≤ (18585137199/200000000000 : ℝ)^15 := by
    have hnat : (153239367 : ℕ)^19*200000000000^15 ≤ 18585137199^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153239367 1000000000 18585137199 200000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(428572793/1000000000 : ℝ), (6373164801/10000000000 : ℝ), (153239367/1000000000 : ℝ)] ![(8547474857433/25000000000000 : ℝ), (11303506391773/20000000000000 : ℝ), (18585137199/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(428572793/1000000000 : ℝ)|^19 ≤ (8547474857433/25000000000000 : ℝ)^15
        have hw : |(428572793/1000000000 : ℝ)|=(428572793/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6373164801/10000000000 : ℝ)|^19 ≤ (11303506391773/20000000000000 : ℝ)^15
        have hw : |(6373164801/10000000000 : ℝ)|=(6373164801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(153239367/1000000000 : ℝ)|^19 ≤ (18585137199/200000000000 : ℝ)^15
        have hw : |(153239367/1000000000 : ℝ)|=(153239367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314052_s1_s1_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2010672517/2500000000 : ℝ)*x 0 + (1442324691/5000000000 : ℝ)*x 1 + (-346799321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010672517/2500000000 : ℝ)^19 ≤ (75888334561279/100000000000000 : ℝ)^15 := by
    have hnat : (2010672517 : ℕ)^19*100000000000000^15 ≤ 75888334561279^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010672517 2500000000 75888334561279 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1442324691/5000000000 : ℝ)^19 ≤ (20707031440799/100000000000000 : ℝ)^15 := by
    have hnat : (1442324691 : ℕ)^19*100000000000000^15 ≤ 20707031440799^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1442324691 5000000000 20707031440799 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (346799321/5000000000 : ℝ)^19 ≤ (3404633984889/100000000000000 : ℝ)^15 := by
    have hnat : (346799321 : ℕ)^19*100000000000000^15 ≤ 3404633984889^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346799321 5000000000 3404633984889 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2010672517/2500000000 : ℝ), (1442324691/5000000000 : ℝ), (-346799321/5000000000 : ℝ)] ![(75888334561279/100000000000000 : ℝ), (20707031440799/100000000000000 : ℝ), (3404633984889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2010672517/2500000000 : ℝ)|^19 ≤ (75888334561279/100000000000000 : ℝ)^15
        have hw : |(2010672517/2500000000 : ℝ)|=(2010672517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1442324691/5000000000 : ℝ)|^19 ≤ (20707031440799/100000000000000 : ℝ)^15
        have hw : |(1442324691/5000000000 : ℝ)|=(1442324691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-346799321/5000000000 : ℝ)|^19 ≤ (3404633984889/100000000000000 : ℝ)^15
        have hw : |(-346799321/5000000000 : ℝ)|=(346799321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314052_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((474/625 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(474/625 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15401/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15401/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-65027/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-65027/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((43457/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43457/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(299/625 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(299/625 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-948/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-948/3125 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s1_pow0 : (474/625 : ℝ) ^ (37/8 : ℝ) ≤ (27831060155594791723/100000000000000000000 : ℝ) := by
    have hpowers : (474/625 : ℝ)^37 ≤ (27831060155594791723/100000000000000000000 : ℝ)^8 := by
      have hnat : (474 : ℕ)^37*100000000000000000000^8 ≤ 27831060155594791723^8*625^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        474 625 27831060155594791723 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (474/625 : ℝ)) (X := (27831060155594791723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (127831060155594791723/100000000000000000000 : ℝ) ≤ (10545241179574813/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (127831060155594791723/100000000000000000000 : ℝ)^8 ≤ (10545241179574813/10000000000000000 : ℝ)^37 := by
      have hnat : (127831060155594791723 : ℕ)^8*10000000000000000^37 ≤ 10545241179574813^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127831060155594791723 100000000000000000000 10545241179574813 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10545241179574813/10000000000000000 : ℝ)) (X := (127831060155594791723/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (77831060155594791723/50000000000000000000 : ℝ) ≤ (11004063009228797/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (77831060155594791723/50000000000000000000 : ℝ)^8 ≤ (11004063009228797/10000000000000000 : ℝ)^37 := by
      have hnat : (77831060155594791723 : ℕ)^8*10000000000000000^37 ≤ 11004063009228797^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77831060155594791723 50000000000000000000 11004063009228797 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11004063009228797/10000000000000000 : ℝ)) (X := (77831060155594791723/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(181747059858271/2528000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(14338182176687/237000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (474/625 : ℝ)) (alpha := (181747059858271/2528000000000000 : ℝ)) (beta := (14338182176687/237000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (474/625 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(181747059858271/2528000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(14338182176687/237000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (15401/20000 : ℝ) ^ (37/8 : ℝ) ≤ (14932070556541308333/50000000000000000000 : ℝ) := by
    have hpowers : (15401/20000 : ℝ)^37 ≤ (14932070556541308333/50000000000000000000 : ℝ)^8 := by
      have hnat : (15401 : ℕ)^37*50000000000000000000^8 ≤ 14932070556541308333^8*20000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15401 20000 14932070556541308333 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15401/20000 : ℝ)) (X := (14932070556541308333/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (64932070556541308333/50000000000000000000 : ℝ) ≤ (2645320054354121/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (64932070556541308333/50000000000000000000 : ℝ)^8 ≤ (2645320054354121/2500000000000000 : ℝ)^37 := by
      have hnat : (64932070556541308333 : ℕ)^8*2500000000000000^37 ≤ 2645320054354121^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64932070556541308333 50000000000000000000 2645320054354121 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2645320054354121/2500000000000000 : ℝ)) (X := (64932070556541308333/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (39932070556541308333/25000000000000000000 : ℝ) ≤ (11065586764797411/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (39932070556541308333/25000000000000000000 : ℝ)^8 ≤ (11065586764797411/10000000000000000 : ℝ)^37 := by
      have hnat : (39932070556541308333 : ℕ)^8*10000000000000000^37 ≤ 11065586764797411^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39932070556541308333 25000000000000000000 11065586764797411 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11065586764797411/10000000000000000 : ℝ)) (X := (39932070556541308333/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(145320054354121/1925125000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(484306547380927/7700500000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (15401/20000 : ℝ)) (alpha := (145320054354121/1925125000000000 : ℝ)) (beta := (484306547380927/7700500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (15401/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(145320054354121/1925125000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(484306547380927/7700500000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (65027/100000 : ℝ) ^ (37/8 : ℝ) ≤ (13663389464609360367/100000000000000000000 : ℝ) := by
    have hpowers : (65027/100000 : ℝ)^37 ≤ (13663389464609360367/100000000000000000000 : ℝ)^8 := by
      have hnat : (65027 : ℕ)^37*100000000000000000000^8 ≤ 13663389464609360367^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65027 100000 13663389464609360367 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (65027/100000 : ℝ)) (X := (13663389464609360367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (113663389464609360367/100000000000000000000 : ℝ) ≤ (5140390124683747/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (113663389464609360367/100000000000000000000 : ℝ)^8 ≤ (5140390124683747/5000000000000000 : ℝ)^37 := by
      have hnat : (113663389464609360367 : ℕ)^8*5000000000000000^37 ≤ 5140390124683747^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113663389464609360367 100000000000000000000 5140390124683747 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5140390124683747/5000000000000000 : ℝ)) (X := (113663389464609360367/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (63663389464609360367/50000000000000000000 : ℝ) ≤ (5268116327615127/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (63663389464609360367/50000000000000000000 : ℝ)^8 ≤ (5268116327615127/5000000000000000 : ℝ)^37 := by
      have hnat : (63663389464609360367 : ℕ)^8*5000000000000000^37 ≤ 5268116327615127^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63663389464609360367 50000000000000000000 5268116327615127 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5268116327615127/5000000000000000 : ℝ)) (X := (63663389464609360367/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(140390124683747/3251350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(6386310146569/162567500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (65027/100000 : ℝ)) (alpha := (140390124683747/3251350000000000 : ℝ)) (beta := (6386310146569/162567500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (65027/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(140390124683747/3251350000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(6386310146569/162567500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1835340057/10000000000 : ℝ)*X 0 0+(1744408707/5000000000 : ℝ)*X 0 1+(-1370854509/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314052_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4845431183/10000000000 : ℝ)*X 2 0+(1158208703/2000000000 : ℝ)*X 2 1+(811803231/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314052_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6564823071/10000000000 : ℝ)*X 0 0+(4172665633/10000000000 : ℝ)*X 0 1+(-1397595521/10000000000 : ℝ)*X 0 2+(6564823071/10000000000 : ℝ)*X 1 0+(4172665633/10000000000 : ℝ)*X 1 1+(-1397595521/10000000000 : ℝ)*X 1 2+(6564823071/10000000000 : ℝ)*X 2 0+(4172665633/10000000000 : ℝ)*X 2 1+(-1397595521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314052_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-812226529/5000000000 : ℝ)*X 0 0+(721470193/2500000000 : ℝ)*X 0 1+(-3742111937/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314052_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1070726909/2500000000 : ℝ)*X 1 0+(-2254851809/10000000000 : ℝ)*X 1 1+(-1461929397/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314052_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2255303973/5000000000 : ℝ)*X 2 0+(3377026411/5000000000 : ℝ)*X 2 1+(144070611/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314052_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((6007765323/10000000000 : ℝ)*X 0 0+(1074821719/2000000000 : ℝ)*X 0 1+(-114635039/2500000000 : ℝ)*X 0 2+(6007765323/10000000000 : ℝ)*X 1 0+(1074821719/2000000000 : ℝ)*X 1 1+(-114635039/2500000000 : ℝ)*X 1 2+(6007765323/10000000000 : ℝ)*X 2 0+(1074821719/2000000000 : ℝ)*X 2 1+(-114635039/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314052_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-892456597/10000000000 : ℝ)*X 0 0+(3352548253/10000000000 : ℝ)*X 0 1+(-3784186581/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314052_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2113243577/5000000000 : ℝ)*X 1 0+(-2520424707/10000000000 : ℝ)*X 1 1+(-5689855377/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314052_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((234049571/400000000 : ℝ)*X 2 0+(5424667687/10000000000 : ℝ)*X 2 1+(329991509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314052_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7631417937/10000000000 : ℝ)*X 0 0+(892153469/2500000000 : ℝ)*X 0 1+(-434169371/10000000000 : ℝ)*X 0 2+(7631417937/10000000000 : ℝ)*X 1 0+(892153469/2500000000 : ℝ)*X 1 1+(-434169371/10000000000 : ℝ)*X 1 2+(7631417937/10000000000 : ℝ)*X 2 0+(892153469/2500000000 : ℝ)*X 2 1+(-434169371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314052_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-107986881/2000000000 : ℝ)*X 0 0+(52062911/125000000 : ℝ)*X 0 1+(-3538887557/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314052_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5976060549/10000000000 : ℝ)*X 1 0+(-1188140753/5000000000 : ℝ)*X 1 1+(-4038092037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314052_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((428572793/1000000000 : ℝ)*X 2 0+(6373164801/10000000000 : ℝ)*X 2 1+(153239367/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314052_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((2010672517/2500000000 : ℝ)*X 0 0+(1442324691/5000000000 : ℝ)*X 0 1+(-346799321/5000000000 : ℝ)*X 0 2+(2010672517/2500000000 : ℝ)*X 1 0+(1442324691/5000000000 : ℝ)*X 1 1+(-346799321/5000000000 : ℝ)*X 1 2+(2010672517/2500000000 : ℝ)*X 2 0+(1442324691/5000000000 : ℝ)*X 2 1+(-346799321/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314052_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((43457/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43457/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (751618681753397930181/39500000000000000000000000 : ℝ) := by norm_num
    linear_combination (764753/250000000000 : ℝ)*(base5) + (418477001937/1000000000000 : ℝ)*(base39) + (129051219553/1000000000000 : ℝ)*(base49) + (601189463581/500000000000 : ℝ)*(base59) + (5032263957687/1000000000000 : ℝ)*(major_s1_0) + (5032263957687/1000000000000 : ℝ)*(major_s1_1) + (5032263957687/1000000000000 : ℝ)*(major_s1_2) + (142799000151/20000000000 : ℝ)*(sp_s1_7) + (7139456273837/1000000000000 : ℝ)*(sp_s1_8) + (3569894160087/500000000000 : ℝ)*(sp_s1_9) + (1462279287401/500000000000 : ℝ)*(sp_s1_13) + (4965617/500000000000 : ℝ)*(sp_s1_14) + (503664947/1000000000000 : ℝ)*(sp_s1_15) + (87338811/500000000000 : ℝ)*(sp_s1_23) + (1462280816907/500000000000 : ℝ)*(f.failure) + (223123748087/31250000000 : ℝ)*(f.sum) + (70007589161236514597/250370206750000000000000000000000 : ℝ)*base62 + (27809335223651/162567500000000000000000000 : ℝ)*base65 + (2797126407449849/7700500000000000000000000000 : ℝ)*base66 + (130256010749029/3251350000000000000000000000 : ℝ)*base69 + (20807355970133687621/164388256000000000000000000000000 : ℝ)*base70 + (14393396481623/79000000000000000000000000 : ℝ)*base73 + (19924824181469/240640625000000000000000000 : ℝ)*base75 + (385230616147177/2528000000000000000000000000 : ℝ)*base77 + (614084682887500781/1216679000000000000000000000000 : ℝ)*base79 + (20583/50000000000000000 : ℝ)*base87 + (20583/50000000000000000 : ℝ)*base89 + (20583/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(299/625 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(299/625 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (102148524032324705887761270439/7911698533300000000000000000000000 : ℝ) := by norm_num
    linear_combination (539660571633/1000000000000 : ℝ)*(base39) + (36493466781/200000000000 : ℝ)*(base49) + (461163714679/500000000000 : ℝ)*(base59) + (1008986192969/200000000000 : ℝ)*(major_s1_0) + (1008986192969/200000000000 : ℝ)*(major_s1_1) + (1008986192969/200000000000 : ℝ)*(major_s1_2) + (3583723/500000000000 : ℝ)*(sp_s1_6) + (17015619/500000000000 : ℝ)*(sp_s1_7) + (12195991/250000000000 : ℝ)*(sp_s1_8) + (7157900375091/1000000000000 : ℝ)*(sp_s1_14) + (1431577124473/200000000000 : ℝ)*(sp_s1_15) + (7157934406329/1000000000000 : ℝ)*(sp_s1_16) + (2931873976639/1000000000000 : ℝ)*(sp_s1_20) + (42075579/1000000000000 : ℝ)*(sp_s1_27) + (586384643933/200000000000 : ℝ)*(f.failure) + (7157934406329/1000000000000 : ℝ)*(f.sum) + (28799938031863800911/50074041350000000000000000000000 : ℝ)*base63 + (15445719032733/650270000000000000000000000 : ℝ)*base64 + (378416664615193/1540100000000000000000000000 : ℝ)*base66 + (174927127205639/325135000000000000000000000 : ℝ)*base69 + (480785577885224507/32877651200000000000000000000000 : ℝ)*base70 + (21571118209697/47400000000000000000000000 : ℝ)*base72 + (210731561666109/385025000000000000000000000 : ℝ)*base75 + (140533999348119/505600000000000000000000000 : ℝ)*base77 + (489566877784921819/730007400000000000000000000000 : ℝ)*base78 + (7377/20000000000000000 : ℝ)*base87 + (7377/20000000000000000 : ℝ)*base89 + (7377/20000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-948/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-948/3125 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (551552969240826892706051/60833950000000000000000000000 : ℝ) := by norm_num
    linear_combination (2592037/500000000000 : ℝ)*(base11) + (223873227581/250000000000 : ℝ)*(base39) + (235880313641/1000000000000 : ℝ)*(base49) + (742714266383/1000000000000 : ℝ)*(base59) + (1837307924849/500000000000 : ℝ)*(major_s1_0) + (1837307924849/500000000000 : ℝ)*(major_s1_1) + (1837307924849/500000000000 : ℝ)*(major_s1_2) + (16658021/1000000000000 : ℝ)*(sp_s1_0) + (1193993/500000000000 : ℝ)*(sp_s1_2) + (13257089/250000000000 : ℝ)*(sp_s1_9) + (65170737171/12500000000 : ℝ)*(sp_s1_21) + (208547232631/40000000000 : ℝ)*(sp_s1_22) + (651703174929/125000000000 : ℝ)*(sp_s1_23) + (1067773930719/500000000000 : ℝ)*(sp_s1_27) + (1067773930719/500000000000 : ℝ)*(f.failure) + (208547232631/40000000000 : ℝ)*(f.sum) + (83319348357577372537/250370206750000000000000000000000 : ℝ)*base63 + (140654631447359/325135000000000000000000000 : ℝ)*base64 + (908022638767001/1925125000000000000000000000 : ℝ)*base67 + (1284846715081559/3251350000000000000000000000 : ℝ)*base68 + (26180738805366957133/82194128000000000000000000000000 : ℝ)*base71 + (118805378616613/118500000000000000000000000 : ℝ)*base73 + (230031869268483/1925125000000000000000000000 : ℝ)*base75 + (10063830251921/1264000000000000000000000000 : ℝ)*base76 + (484458080820860561/1825018500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (12389/50000000000000000 : ℝ)*base86 + (12389/50000000000000000 : ℝ)*base88 + (12389/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((474/625 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(474/625 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15401/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15401/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-65027/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-65027/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((43457/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43457/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(299/625 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(299/625 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-948/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-948/3125 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314052_s1 p hpa hpb X hX hprev0

#print axioms solution

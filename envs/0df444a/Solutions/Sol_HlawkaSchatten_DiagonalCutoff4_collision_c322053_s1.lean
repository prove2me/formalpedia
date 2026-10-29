-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c322053_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:46:52.913626+00:00
-- url     : https://prove2.me/submissions/9f897d7c-08b3-421f-bdab-4e50e69db864

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
theorem collision_support_c322053_s1_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-15089391/78125000 : ℝ)*x 0 + (5059696417/10000000000 : ℝ)*x 1 + (2561947049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15089391/78125000 : ℝ)^21 ≤ (3279395912281/25000000000000 : ℝ)^17 := by
    have hnat : (15089391 : ℕ)^21*25000000000000^17 ≤ 3279395912281^17*78125000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15089391 78125000 3279395912281 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5059696417/10000000000 : ℝ)^21 ≤ (43102919338179/100000000000000 : ℝ)^17 := by
    have hnat : (5059696417 : ℕ)^21*100000000000000^17 ≤ 43102919338179^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5059696417 10000000000 43102919338179 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2561947049/5000000000 : ℝ)^21 ≤ (5472437124221/12500000000000 : ℝ)^17 := by
    have hnat : (2561947049 : ℕ)^21*12500000000000^17 ≤ 5472437124221^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2561947049 5000000000 5472437124221 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15089391/78125000 : ℝ), (5059696417/10000000000 : ℝ), (2561947049/5000000000 : ℝ)] ![(3279395912281/25000000000000 : ℝ), (43102919338179/100000000000000 : ℝ), (5472437124221/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15089391/78125000 : ℝ)|^21 ≤ (3279395912281/25000000000000 : ℝ)^17
        have hw : |(-15089391/78125000 : ℝ)|=(15089391/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5059696417/10000000000 : ℝ)|^21 ≤ (43102919338179/100000000000000 : ℝ)^17
        have hw : |(5059696417/10000000000 : ℝ)|=(5059696417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2561947049/5000000000 : ℝ)|^21 ≤ (5472437124221/12500000000000 : ℝ)^17
        have hw : |(2561947049/5000000000 : ℝ)|=(2561947049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322053_s1_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1115223757/2500000000 : ℝ)*x 0 + (-1333586679/10000000000 : ℝ)*x 1 + (192056693/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1115223757/2500000000 : ℝ)^21 ≤ (18446036673771/50000000000000 : ℝ)^17 := by
    have hnat : (1115223757 : ℕ)^21*50000000000000^17 ≤ 18446036673771^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115223757 2500000000 18446036673771 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1333586679/10000000000 : ℝ)^21 ≤ (8301257688809/100000000000000 : ℝ)^17 := by
    have hnat : (1333586679 : ℕ)^21*100000000000000^17 ≤ 8301257688809^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333586679 10000000000 8301257688809 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (192056693/312500000 : ℝ)^21 ≤ (27403334470261/50000000000000 : ℝ)^17 := by
    have hnat : (192056693 : ℕ)^21*50000000000000^17 ≤ 27403334470261^17*312500000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192056693 312500000 27403334470261 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1115223757/2500000000 : ℝ), (-1333586679/10000000000 : ℝ), (192056693/312500000 : ℝ)] ![(18446036673771/50000000000000 : ℝ), (8301257688809/100000000000000 : ℝ), (27403334470261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1115223757/2500000000 : ℝ)|^21 ≤ (18446036673771/50000000000000 : ℝ)^17
        have hw : |(1115223757/2500000000 : ℝ)|=(1115223757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1333586679/10000000000 : ℝ)|^21 ≤ (8301257688809/100000000000000 : ℝ)^17
        have hw : |(-1333586679/10000000000 : ℝ)|=(1333586679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(192056693/312500000 : ℝ)|^21 ≤ (27403334470261/50000000000000 : ℝ)^17
        have hw : |(192056693/312500000 : ℝ)|=(192056693/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322053_s1_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1120838587/2500000000 : ℝ)*x 0 + (3073707603/5000000000 : ℝ)*x 1 + (-260268791/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120838587/2500000000 : ℝ)^21 ≤ (37121653781033/100000000000000 : ℝ)^17 := by
    have hnat : (1120838587 : ℕ)^21*100000000000000^17 ≤ 37121653781033^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120838587 2500000000 37121653781033 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3073707603/5000000000 : ℝ)^21 ≤ (27412153222451/50000000000000 : ℝ)^17 := by
    have hnat : (3073707603 : ℕ)^21*50000000000000^17 ≤ 27412153222451^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3073707603 5000000000 27412153222451 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260268791/2000000000 : ℝ)^21 ≤ (8054039762901/100000000000000 : ℝ)^17 := by
    have hnat : (260268791 : ℕ)^21*100000000000000^17 ≤ 8054039762901^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260268791 2000000000 8054039762901 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120838587/2500000000 : ℝ), (3073707603/5000000000 : ℝ), (-260268791/2000000000 : ℝ)] ![(37121653781033/100000000000000 : ℝ), (27412153222451/50000000000000 : ℝ), (8054039762901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120838587/2500000000 : ℝ)|^21 ≤ (37121653781033/100000000000000 : ℝ)^17
        have hw : |(1120838587/2500000000 : ℝ)|=(1120838587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3073707603/5000000000 : ℝ)|^21 ≤ (27412153222451/50000000000000 : ℝ)^17
        have hw : |(3073707603/5000000000 : ℝ)|=(3073707603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-260268791/2000000000 : ℝ)|^21 ≤ (8054039762901/100000000000000 : ℝ)^17
        have hw : |(-260268791/2000000000 : ℝ)|=(260268791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322053_s1_s1_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1835634129/10000000000 : ℝ)*x 0 + (4072397599/10000000000 : ℝ)*x 1 + (6137643521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1835634129/10000000000 : ℝ)^21 ≤ (6159271293819/50000000000000 : ℝ)^17 := by
    have hnat : (1835634129 : ℕ)^21*50000000000000^17 ≤ 6159271293819^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1835634129 10000000000 6159271293819 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4072397599/10000000000 : ℝ)^21 ≤ (1648239120173/5000000000000 : ℝ)^17 := by
    have hnat : (4072397599 : ℕ)^21*5000000000000^17 ≤ 1648239120173^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4072397599 10000000000 1648239120173 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6137643521/10000000000 : ℝ)^21 ≤ (10943334999797/20000000000000 : ℝ)^17 := by
    have hnat : (6137643521 : ℕ)^21*20000000000000^17 ≤ 10943334999797^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6137643521 10000000000 10943334999797 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1835634129/10000000000 : ℝ), (4072397599/10000000000 : ℝ), (6137643521/10000000000 : ℝ)] ![(6159271293819/50000000000000 : ℝ), (1648239120173/5000000000000 : ℝ), (10943334999797/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1835634129/10000000000 : ℝ)|^21 ≤ (6159271293819/50000000000000 : ℝ)^17
        have hw : |(-1835634129/10000000000 : ℝ)|=(1835634129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4072397599/10000000000 : ℝ)|^21 ≤ (1648239120173/5000000000000 : ℝ)^17
        have hw : |(4072397599/10000000000 : ℝ)|=(4072397599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6137643521/10000000000 : ℝ)|^21 ≤ (10943334999797/20000000000000 : ℝ)^17
        have hw : |(6137643521/10000000000 : ℝ)|=(6137643521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322053_s1_s1_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2053493499/5000000000 : ℝ)*x 0 + (-986859367/10000000000 : ℝ)*x 1 + (6699223659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2053493499/5000000000 : ℝ)^21 ≤ (33310997695843/100000000000000 : ℝ)^17 := by
    have hnat : (2053493499 : ℕ)^21*100000000000000^17 ≤ 33310997695843^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053493499 5000000000 33310997695843 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (986859367/10000000000 : ℝ)^21 ≤ (5722811593681/100000000000000 : ℝ)^17 := by
    have hnat : (986859367 : ℕ)^21*100000000000000^17 ≤ 5722811593681^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986859367 10000000000 5722811593681 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6699223659/10000000000 : ℝ)^21 ≤ (12193238139829/20000000000000 : ℝ)^17 := by
    have hnat : (6699223659 : ℕ)^21*20000000000000^17 ≤ 12193238139829^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6699223659 10000000000 12193238139829 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2053493499/5000000000 : ℝ), (-986859367/10000000000 : ℝ), (6699223659/10000000000 : ℝ)] ![(33310997695843/100000000000000 : ℝ), (5722811593681/100000000000000 : ℝ), (12193238139829/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2053493499/5000000000 : ℝ)|^21 ≤ (33310997695843/100000000000000 : ℝ)^17
        have hw : |(2053493499/5000000000 : ℝ)|=(2053493499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-986859367/10000000000 : ℝ)|^21 ≤ (5722811593681/100000000000000 : ℝ)^17
        have hw : |(-986859367/10000000000 : ℝ)|=(986859367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6699223659/10000000000 : ℝ)|^21 ≤ (12193238139829/20000000000000 : ℝ)^17
        have hw : |(6699223659/10000000000 : ℝ)|=(6699223659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322053_s1_s1_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1032415259/2500000000 : ℝ)*x 0 + (880622823/1250000000 : ℝ)*x 1 + (-349088243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1032415259/2500000000 : ℝ)^21 ≤ (26201813767/78125000000 : ℝ)^17 := by
    have hnat : (1032415259 : ℕ)^21*78125000000^17 ≤ 26201813767^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032415259 2500000000 26201813767 78125000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (880622823/1250000000 : ℝ)^21 ≤ (12975286629841/20000000000000 : ℝ)^17 := by
    have hnat : (880622823 : ℕ)^21*20000000000000^17 ≤ 12975286629841^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880622823 1250000000 12975286629841 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (349088243/10000000000 : ℝ)^21 ≤ (1585245215811/100000000000000 : ℝ)^17 := by
    have hnat : (349088243 : ℕ)^21*100000000000000^17 ≤ 1585245215811^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349088243 10000000000 1585245215811 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1032415259/2500000000 : ℝ), (880622823/1250000000 : ℝ), (-349088243/10000000000 : ℝ)] ![(26201813767/78125000000 : ℝ), (12975286629841/20000000000000 : ℝ), (1585245215811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1032415259/2500000000 : ℝ)|^21 ≤ (26201813767/78125000000 : ℝ)^17
        have hw : |(1032415259/2500000000 : ℝ)|=(1032415259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(880622823/1250000000 : ℝ)|^21 ≤ (12975286629841/20000000000000 : ℝ)^17
        have hw : |(880622823/1250000000 : ℝ)|=(880622823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-349088243/10000000000 : ℝ)|^21 ≤ (1585245215811/100000000000000 : ℝ)^17
        have hw : |(-349088243/10000000000 : ℝ)|=(349088243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322053_s1_s1_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (42944823/62500000 : ℝ)*x 0 + (497786923/1250000000 : ℝ)*x 1 + (888805003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42944823/62500000 : ℝ)^21 ≤ (62904991150347/100000000000000 : ℝ)^17 := by
    have hnat : (42944823 : ℕ)^21*100000000000000^17 ≤ 62904991150347^17*62500000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42944823 62500000 62904991150347 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (497786923/1250000000 : ℝ)^21 ≤ (6413236029681/20000000000000 : ℝ)^17 := by
    have hnat : (497786923 : ℕ)^21*20000000000000^17 ≤ 6413236029681^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497786923 1250000000 6413236029681 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (888805003/10000000000 : ℝ)^21 ≤ (5028828688633/100000000000000 : ℝ)^17 := by
    have hnat : (888805003 : ℕ)^21*100000000000000^17 ≤ 5028828688633^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888805003 10000000000 5028828688633 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42944823/62500000 : ℝ), (497786923/1250000000 : ℝ), (888805003/10000000000 : ℝ)] ![(62904991150347/100000000000000 : ℝ), (6413236029681/20000000000000 : ℝ), (5028828688633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42944823/62500000 : ℝ)|^21 ≤ (62904991150347/100000000000000 : ℝ)^17
        have hw : |(42944823/62500000 : ℝ)|=(42944823/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(497786923/1250000000 : ℝ)|^21 ≤ (6413236029681/20000000000000 : ℝ)^17
        have hw : |(497786923/1250000000 : ℝ)|=(497786923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(888805003/10000000000 : ℝ)|^21 ≤ (5028828688633/100000000000000 : ℝ)^17
        have hw : |(888805003/10000000000 : ℝ)|=(888805003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322053_s1_s1_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-892652171/10000000000 : ℝ)*x 0 + (2424099997/5000000000 : ℝ)*x 1 + (1519393729/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892652171/10000000000 : ℝ)^21 ≤ (2527865597187/50000000000000 : ℝ)^17 := by
    have hnat : (892652171 : ℕ)^21*50000000000000^17 ≤ 2527865597187^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892652171 10000000000 2527865597187 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2424099997/5000000000 : ℝ)^21 ≤ (8177667903649/20000000000000 : ℝ)^17 := by
    have hnat : (2424099997 : ℕ)^21*20000000000000^17 ≤ 8177667903649^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2424099997 5000000000 8177667903649 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1519393729/2500000000 : ℝ)^21 ≤ (54055929265581/100000000000000 : ℝ)^17 := by
    have hnat : (1519393729 : ℕ)^21*100000000000000^17 ≤ 54055929265581^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519393729 2500000000 54055929265581 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-892652171/10000000000 : ℝ), (2424099997/5000000000 : ℝ), (1519393729/2500000000 : ℝ)] ![(2527865597187/50000000000000 : ℝ), (8177667903649/20000000000000 : ℝ), (54055929265581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-892652171/10000000000 : ℝ)|^21 ≤ (2527865597187/50000000000000 : ℝ)^17
        have hw : |(-892652171/10000000000 : ℝ)|=(892652171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2424099997/5000000000 : ℝ)|^21 ≤ (8177667903649/20000000000000 : ℝ)^17
        have hw : |(2424099997/5000000000 : ℝ)|=(2424099997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1519393729/2500000000 : ℝ)|^21 ≤ (54055929265581/100000000000000 : ℝ)^17
        have hw : |(1519393729/2500000000 : ℝ)|=(1519393729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322053_s1_s1_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1026365149/2500000000 : ℝ)*x 0 + (-976536893/10000000000 : ℝ)*x 1 + (1676788119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026365149/2500000000 : ℝ)^21 ≤ (1664785248997/5000000000000 : ℝ)^17 := by
    have hnat : (1026365149 : ℕ)^21*5000000000000^17 ≤ 1664785248997^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026365149 2500000000 1664785248997 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (976536893/10000000000 : ℝ)^21 ≤ (5648957911113/100000000000000 : ℝ)^17 := by
    have hnat : (976536893 : ℕ)^21*100000000000000^17 ≤ 5648957911113^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976536893 10000000000 5648957911113 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1676788119/2500000000 : ℝ)^21 ≤ (61055337097021/100000000000000 : ℝ)^17 := by
    have hnat : (1676788119 : ℕ)^21*100000000000000^17 ≤ 61055337097021^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676788119 2500000000 61055337097021 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1026365149/2500000000 : ℝ), (-976536893/10000000000 : ℝ), (1676788119/2500000000 : ℝ)] ![(1664785248997/5000000000000 : ℝ), (5648957911113/100000000000000 : ℝ), (61055337097021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1026365149/2500000000 : ℝ)|^21 ≤ (1664785248997/5000000000000 : ℝ)^17
        have hw : |(1026365149/2500000000 : ℝ)|=(1026365149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-976536893/10000000000 : ℝ)|^21 ≤ (5648957911113/100000000000000 : ℝ)^17
        have hw : |(-976536893/10000000000 : ℝ)|=(976536893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1676788119/2500000000 : ℝ)|^21 ≤ (61055337097021/100000000000000 : ℝ)^17
        have hw : |(1676788119/2500000000 : ℝ)|=(1676788119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322053_s1_s1_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5583538111/10000000000 : ℝ)*x 0 + (564931583/1000000000 : ℝ)*x 1 + (-409156881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5583538111/10000000000 : ℝ)^21 ≤ (9736183958859/20000000000000 : ℝ)^17 := by
    have hnat : (5583538111 : ℕ)^21*20000000000000^17 ≤ 9736183958859^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5583538111 10000000000 9736183958859 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564931583/1000000000 : ℝ)^21 ≤ (49390331213747/100000000000000 : ℝ)^17 := by
    have hnat : (564931583 : ℕ)^21*100000000000000^17 ≤ 49390331213747^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564931583 1000000000 49390331213747 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (409156881/10000000000 : ℝ)^21 ≤ (1928748976357/100000000000000 : ℝ)^17 := by
    have hnat : (409156881 : ℕ)^21*100000000000000^17 ≤ 1928748976357^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409156881 10000000000 1928748976357 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5583538111/10000000000 : ℝ), (564931583/1000000000 : ℝ), (-409156881/10000000000 : ℝ)] ![(9736183958859/20000000000000 : ℝ), (49390331213747/100000000000000 : ℝ), (1928748976357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5583538111/10000000000 : ℝ)|^21 ≤ (9736183958859/20000000000000 : ℝ)^17
        have hw : |(5583538111/10000000000 : ℝ)|=(5583538111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564931583/1000000000 : ℝ)|^21 ≤ (49390331213747/100000000000000 : ℝ)^17
        have hw : |(564931583/1000000000 : ℝ)|=(564931583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-409156881/10000000000 : ℝ)|^21 ≤ (1928748976357/100000000000000 : ℝ)^17
        have hw : |(-409156881/10000000000 : ℝ)|=(409156881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322053_s1_s1_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1667318741/2000000000 : ℝ)*x 0 + (1091338313/5000000000 : ℝ)*x 1 + (866130101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1667318741/2000000000 : ℝ)^21 ≤ (15974516512687/20000000000000 : ℝ)^17 := by
    have hnat : (1667318741 : ℕ)^21*20000000000000^17 ≤ 15974516512687^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1667318741 2000000000 15974516512687 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091338313/5000000000 : ℝ)^21 ≤ (1907073819897/12500000000000 : ℝ)^17 := by
    have hnat : (1091338313 : ℕ)^21*12500000000000^17 ≤ 1907073819897^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091338313 5000000000 1907073819897 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (866130101/10000000000 : ℝ)^21 ≤ (243541343173/5000000000000 : ℝ)^17 := by
    have hnat : (866130101 : ℕ)^21*5000000000000^17 ≤ 243541343173^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866130101 10000000000 243541343173 5000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1667318741/2000000000 : ℝ), (1091338313/5000000000 : ℝ), (866130101/10000000000 : ℝ)] ![(15974516512687/20000000000000 : ℝ), (1907073819897/12500000000000 : ℝ), (243541343173/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1667318741/2000000000 : ℝ)|^21 ≤ (15974516512687/20000000000000 : ℝ)^17
        have hw : |(1667318741/2000000000 : ℝ)|=(1667318741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091338313/5000000000 : ℝ)|^21 ≤ (1907073819897/12500000000000 : ℝ)^17
        have hw : |(1091338313/5000000000 : ℝ)|=(1091338313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(866130101/10000000000 : ℝ)|^21 ≤ (243541343173/5000000000000 : ℝ)^17
        have hw : |(866130101/10000000000 : ℝ)|=(866130101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322053_s1_s1_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-206179761/2500000000 : ℝ)*x 0 + (2816135093/5000000000 : ℝ)*x 1 + (5352879403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206179761/2500000000 : ℝ)^21 ≤ (916957486761/20000000000000 : ℝ)^17 := by
    have hnat : (206179761 : ℕ)^21*20000000000000^17 ≤ 916957486761^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206179761 2500000000 916957486761 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2816135093/5000000000 : ℝ)^21 ≤ (12301576687519/25000000000000 : ℝ)^17 := by
    have hnat : (2816135093 : ℕ)^21*25000000000000^17 ≤ 12301576687519^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2816135093 5000000000 12301576687519 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5352879403/10000000000 : ℝ)^21 ≤ (46208905798547/100000000000000 : ℝ)^17 := by
    have hnat : (5352879403 : ℕ)^21*100000000000000^17 ≤ 46208905798547^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352879403 10000000000 46208905798547 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-206179761/2500000000 : ℝ), (2816135093/5000000000 : ℝ), (5352879403/10000000000 : ℝ)] ![(916957486761/20000000000000 : ℝ), (12301576687519/25000000000000 : ℝ), (46208905798547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-206179761/2500000000 : ℝ)|^21 ≤ (916957486761/20000000000000 : ℝ)^17
        have hw : |(-206179761/2500000000 : ℝ)|=(206179761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2816135093/5000000000 : ℝ)|^21 ≤ (12301576687519/25000000000000 : ℝ)^17
        have hw : |(2816135093/5000000000 : ℝ)|=(2816135093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5352879403/10000000000 : ℝ)|^21 ≤ (46208905798547/100000000000000 : ℝ)^17
        have hw : |(5352879403/10000000000 : ℝ)|=(5352879403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322053_s1_s1_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1407199291/2500000000 : ℝ)*x 0 + (-62424573/1250000000 : ℝ)*x 1 + (5554094947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1407199291/2500000000 : ℝ)^21 ≤ (24584414060981/50000000000000 : ℝ)^17 := by
    have hnat : (1407199291 : ℕ)^21*50000000000000^17 ≤ 24584414060981^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1407199291 2500000000 24584414060981 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62424573/1250000000 : ℝ)^21 ≤ (2467160853919/100000000000000 : ℝ)^17 := by
    have hnat : (62424573 : ℕ)^21*100000000000000^17 ≤ 2467160853919^17*1250000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62424573 1250000000 2467160853919 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5554094947/10000000000 : ℝ)^21 ≤ (48364011016487/100000000000000 : ℝ)^17 := by
    have hnat : (5554094947 : ℕ)^21*100000000000000^17 ≤ 48364011016487^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5554094947 10000000000 48364011016487 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1407199291/2500000000 : ℝ), (-62424573/1250000000 : ℝ), (5554094947/10000000000 : ℝ)] ![(24584414060981/50000000000000 : ℝ), (2467160853919/100000000000000 : ℝ), (48364011016487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1407199291/2500000000 : ℝ)|^21 ≤ (24584414060981/50000000000000 : ℝ)^17
        have hw : |(1407199291/2500000000 : ℝ)|=(1407199291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-62424573/1250000000 : ℝ)|^21 ≤ (2467160853919/100000000000000 : ℝ)^17
        have hw : |(-62424573/1250000000 : ℝ)|=(62424573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5554094947/10000000000 : ℝ)|^21 ≤ (48364011016487/100000000000000 : ℝ)^17
        have hw : |(5554094947/10000000000 : ℝ)|=(5554094947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322053_s1_s1_23 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4036331723/10000000000 : ℝ)*x 0 + (688256251/1000000000 : ℝ)*x 1 + (-396035513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4036331723/10000000000 : ℝ)^21 ≤ (32604524809737/100000000000000 : ℝ)^17 := by
    have hnat : (4036331723 : ℕ)^21*100000000000000^17 ≤ 32604524809737^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036331723 10000000000 32604524809737 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688256251/1000000000 : ℝ)^21 ≤ (15758458825239/25000000000000 : ℝ)^17 := by
    have hnat : (688256251 : ℕ)^21*25000000000000^17 ≤ 15758458825239^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688256251 1000000000 15758458825239 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396035513/5000000000 : ℝ)^21 ≤ (4361639869381/100000000000000 : ℝ)^17 := by
    have hnat : (396035513 : ℕ)^21*100000000000000^17 ≤ 4361639869381^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396035513 5000000000 4361639869381 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4036331723/10000000000 : ℝ), (688256251/1000000000 : ℝ), (-396035513/5000000000 : ℝ)] ![(32604524809737/100000000000000 : ℝ), (15758458825239/25000000000000 : ℝ), (4361639869381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4036331723/10000000000 : ℝ)|^21 ≤ (32604524809737/100000000000000 : ℝ)^17
        have hw : |(4036331723/10000000000 : ℝ)|=(4036331723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688256251/1000000000 : ℝ)|^21 ≤ (15758458825239/25000000000000 : ℝ)^17
        have hw : |(688256251/1000000000 : ℝ)|=(688256251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-396035513/5000000000 : ℝ)|^21 ≤ (4361639869381/100000000000000 : ℝ)^17
        have hw : |(-396035513/5000000000 : ℝ)|=(396035513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322053_s1_s1_27 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4299566727/5000000000 : ℝ)*x 0 + (689953291/5000000000 : ℝ)*x 1 + (1339907099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299566727/5000000000 : ℝ)^21 ≤ (10373905222951/12500000000000 : ℝ)^17 := by
    have hnat : (4299566727 : ℕ)^21*12500000000000^17 ≤ 10373905222951^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299566727 5000000000 10373905222951 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (689953291/5000000000 : ℝ)^21 ≤ (1731774628621/20000000000000 : ℝ)^17 := by
    have hnat : (689953291 : ℕ)^21*20000000000000^17 ≤ 1731774628621^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689953291 5000000000 1731774628621 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1339907099/10000000000 : ℝ)^21 ≤ (8349885055581/100000000000000 : ℝ)^17 := by
    have hnat : (1339907099 : ℕ)^21*100000000000000^17 ≤ 8349885055581^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339907099 10000000000 8349885055581 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299566727/5000000000 : ℝ), (689953291/5000000000 : ℝ), (1339907099/10000000000 : ℝ)] ![(10373905222951/12500000000000 : ℝ), (1731774628621/20000000000000 : ℝ), (8349885055581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299566727/5000000000 : ℝ)|^21 ≤ (10373905222951/12500000000000 : ℝ)^17
        have hw : |(4299566727/5000000000 : ℝ)|=(4299566727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(689953291/5000000000 : ℝ)|^21 ≤ (1731774628621/20000000000000 : ℝ)^17
        have hw : |(689953291/5000000000 : ℝ)|=(689953291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1339907099/10000000000 : ℝ)|^21 ≤ (8349885055581/100000000000000 : ℝ)^17
        have hw : |(1339907099/10000000000 : ℝ)|=(1339907099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322053_s1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((70597/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(70597/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70657/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70657/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69197/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(69197/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18309/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18309/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43269/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43269/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10287/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10287/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s1_pow0 : (70597/100000 : ℝ) ^ (41/8 : ℝ) ≤ (8394590513950640047/50000000000000000000 : ℝ) := by
    have hpowers : (70597/100000 : ℝ)^41 ≤ (8394590513950640047/50000000000000000000 : ℝ)^8 := by
      have hnat : (70597 : ℕ)^41*50000000000000000000^8 ≤ 8394590513950640047^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70597 100000 8394590513950640047 50000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (70597/100000 : ℝ)) (X := (8394590513950640047/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (58394590513950640047/50000000000000000000 : ℝ) ≤ (1030746169102569/1000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (58394590513950640047/50000000000000000000 : ℝ)^8 ≤ (1030746169102569/1000000000000000 : ℝ)^41 := by
      have hnat : (58394590513950640047 : ℕ)^8*1000000000000000^41 ≤ 1030746169102569^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58394590513950640047 50000000000000000000 1030746169102569 1000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1030746169102569/1000000000000000 : ℝ)) (X := (58394590513950640047/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (33394590513950640047/25000000000000000000 : ℝ) ≤ (1322646810158033/1250000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (33394590513950640047/25000000000000000000 : ℝ)^8 ≤ (1322646810158033/1250000000000000 : ℝ)^41 := by
      have hnat : (33394590513950640047 : ℕ)^8*1250000000000000^41 ≤ 1322646810158033^41*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33394590513950640047 25000000000000000000 1322646810158033 1250000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1322646810158033/1250000000000000 : ℝ)) (X := (33394590513950640047/25000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(30746169102569/705970000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(136856395119287/3529850000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (70597/100000 : ℝ)) (alpha := (30746169102569/705970000000000 : ℝ)) (beta := (136856395119287/3529850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (70597/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(30746169102569/705970000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(136856395119287/3529850000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (70657/100000 : ℝ) ^ (41/8 : ℝ) ≤ (16862438119125722541/100000000000000000000 : ℝ) := by
    have hpowers : (70657/100000 : ℝ)^41 ≤ (16862438119125722541/100000000000000000000 : ℝ)^8 := by
      have hnat : (70657 : ℕ)^41*100000000000000000000^8 ≤ 16862438119125722541^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70657 100000 16862438119125722541 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (70657/100000 : ℝ)) (X := (16862438119125722541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (116862438119125722541/100000000000000000000 : ℝ) ≤ (10308722923992467/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (116862438119125722541/100000000000000000000 : ℝ)^8 ≤ (10308722923992467/10000000000000000 : ℝ)^41 := by
      have hnat : (116862438119125722541 : ℕ)^8*10000000000000000^41 ≤ 10308722923992467^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116862438119125722541 100000000000000000000 10308722923992467 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10308722923992467/10000000000000000 : ℝ)) (X := (116862438119125722541/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (66862438119125722541/50000000000000000000 : ℝ) ≤ (5291719020447497/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (66862438119125722541/50000000000000000000 : ℝ)^8 ≤ (5291719020447497/5000000000000000 : ℝ)^41 := by
      have hnat : (66862438119125722541 : ℕ)^8*5000000000000000^41 ≤ 5291719020447497^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66862438119125722541 50000000000000000000 5291719020447497 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5291719020447497/5000000000000000 : ℝ)) (X := (66862438119125722541/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(308722923992467/7065700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(274715116902527/7065700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (70657/100000 : ℝ)) (alpha := (308722923992467/7065700000000000 : ℝ)) (beta := (274715116902527/7065700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (70657/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(308722923992467/7065700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(274715116902527/7065700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (69197/100000 : ℝ) ^ (41/8 : ℝ) ≤ (15151207274224035767/100000000000000000000 : ℝ) := by
    have hpowers : (69197/100000 : ℝ)^41 ≤ (15151207274224035767/100000000000000000000 : ℝ)^8 := by
      have hnat : (69197 : ℕ)^41*100000000000000000000^8 ≤ 15151207274224035767^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69197 100000 15151207274224035767 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69197/100000 : ℝ)) (X := (15151207274224035767/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (115151207274224035767/100000000000000000000 : ℝ) ≤ (642443361394187/625000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (115151207274224035767/100000000000000000000 : ℝ)^8 ≤ (642443361394187/625000000000000 : ℝ)^41 := by
      have hnat : (115151207274224035767 : ℕ)^8*625000000000000^41 ≤ 642443361394187^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        115151207274224035767 100000000000000000000 642443361394187 625000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (642443361394187/625000000000000 : ℝ)) (X := (115151207274224035767/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (65151207274224035767/50000000000000000000 : ℝ) ≤ (5265016702922399/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (65151207274224035767/50000000000000000000 : ℝ)^8 ≤ (5265016702922399/5000000000000000 : ℝ)^41 := by
      have hnat : (65151207274224035767 : ℕ)^8*5000000000000000^41 ≤ 5265016702922399^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65151207274224035767 50000000000000000000 5265016702922399 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5265016702922399/5000000000000000 : ℝ)) (X := (65151207274224035767/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(17443361394187/432481250000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(125469811768903/3459850000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (69197/100000 : ℝ)) (alpha := (17443361394187/432481250000000 : ℝ)) (beta := (125469811768903/3459850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (69197/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(17443361394187/432481250000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(125469811768903/3459850000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-15089391/78125000 : ℝ)*X 0 0+(5059696417/10000000000 : ℝ)*X 0 1+(2561947049/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322053_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1115223757/2500000000 : ℝ)*X 1 0+(-1333586679/10000000000 : ℝ)*X 1 1+(192056693/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322053_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1120838587/2500000000 : ℝ)*X 2 0+(3073707603/5000000000 : ℝ)*X 2 1+(-260268791/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322053_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1835634129/10000000000 : ℝ)*X 0 0+(4072397599/10000000000 : ℝ)*X 0 1+(6137643521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322053_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2053493499/5000000000 : ℝ)*X 1 0+(-986859367/10000000000 : ℝ)*X 1 1+(6699223659/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322053_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1032415259/2500000000 : ℝ)*X 2 0+(880622823/1250000000 : ℝ)*X 2 1+(-349088243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322053_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((42944823/62500000 : ℝ)*X 0 0+(497786923/1250000000 : ℝ)*X 0 1+(888805003/10000000000 : ℝ)*X 0 2+(42944823/62500000 : ℝ)*X 1 0+(497786923/1250000000 : ℝ)*X 1 1+(888805003/10000000000 : ℝ)*X 1 2+(42944823/62500000 : ℝ)*X 2 0+(497786923/1250000000 : ℝ)*X 2 1+(888805003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322053_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-892652171/10000000000 : ℝ)*X 0 0+(2424099997/5000000000 : ℝ)*X 0 1+(1519393729/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322053_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1026365149/2500000000 : ℝ)*X 1 0+(-976536893/10000000000 : ℝ)*X 1 1+(1676788119/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322053_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((5583538111/10000000000 : ℝ)*X 2 0+(564931583/1000000000 : ℝ)*X 2 1+(-409156881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322053_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1667318741/2000000000 : ℝ)*X 0 0+(1091338313/5000000000 : ℝ)*X 0 1+(866130101/10000000000 : ℝ)*X 0 2+(1667318741/2000000000 : ℝ)*X 1 0+(1091338313/5000000000 : ℝ)*X 1 1+(866130101/10000000000 : ℝ)*X 1 2+(1667318741/2000000000 : ℝ)*X 2 0+(1091338313/5000000000 : ℝ)*X 2 1+(866130101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322053_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-206179761/2500000000 : ℝ)*X 0 0+(2816135093/5000000000 : ℝ)*X 0 1+(5352879403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322053_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1407199291/2500000000 : ℝ)*X 1 0+(-62424573/1250000000 : ℝ)*X 1 1+(5554094947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322053_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4036331723/10000000000 : ℝ)*X 2 0+(688256251/1000000000 : ℝ)*X 2 1+(-396035513/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322053_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((4299566727/5000000000 : ℝ)*X 0 0+(689953291/5000000000 : ℝ)*X 0 1+(1339907099/10000000000 : ℝ)*X 0 2+(4299566727/5000000000 : ℝ)*X 1 0+(689953291/5000000000 : ℝ)*X 1 1+(1339907099/10000000000 : ℝ)*X 1 2+(4299566727/5000000000 : ℝ)*X 2 0+(689953291/5000000000 : ℝ)*X 2 1+(1339907099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322053_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((18309/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18309/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1212348070939050995608280043/244462621450000000000000000000000 : ℝ) := by norm_num
    linear_combination (3203101/1000000000000 : ℝ)*(base19) + (13463153837/500000000000 : ℝ)*(base49) + (744501951991/1000000000000 : ℝ)*(base59) + (2418408656459/500000000000 : ℝ)*(major_s1_0) + (2418408656459/500000000000 : ℝ)*(major_s1_1) + (2418408656459/500000000000 : ℝ)*(major_s1_2) + (5376713/125000000000 : ℝ)*(sp_s1_0) + (7167335043831/1000000000000 : ℝ)*(sp_s1_7) + (7167351213357/1000000000000 : ℝ)*(sp_s1_8) + (3583629188569/500000000000 : ℝ)*(sp_s1_9) + (62656320443/25000000000 : ℝ)*(sp_s1_13) + (839/400000000 : ℝ)*(sp_s1_14) + (25738577/1000000000000 : ℝ)*(sp_s1_15) + (121777897/1000000000000 : ℝ)*(sp_s1_23) + (62656320443/25000000000 : ℝ)*(f.failure) + (1433476031007/200000000000 : ℝ)*(f.sum) + (668612078039473529/30557827681250000000000000000000 : ℝ)*base63 + (273079505926301/3459850000000000000000000000 : ℝ)*base65 + (30420374819047/220803125000000000000000000 : ℝ)*base67 + (219605565089999/1729925000000000000000000000 : ℝ)*base69 + (5365644821192691917/61063757612500000000000000000000 : ℝ)*base70 + (908321368570591/3529850000000000000000000000 : ℝ)*base73 + (372275675492069/1766425000000000000000000000 : ℝ)*base75 + (3580483514149/22061562500000000000000000 : ℝ)*base77 + (16226413523127439039/249408611450000000000000000000000 : ℝ)*base78 + (43/250000000000000 : ℝ)*base86 + (43/250000000000000 : ℝ)*base88 + (43/250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43269/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43269/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1072359000244295558387196111/244462621450000000000000000000000 : ℝ) := by norm_num
    linear_combination (72527873763/1000000000000 : ℝ)*(base49) + (90177564647/500000000000 : ℝ)*(base59) + (4636778793387/1000000000000 : ℝ)*(major_s1_0) + (4636778793387/1000000000000 : ℝ)*(major_s1_1) + (4636778793387/1000000000000 : ℝ)*(major_s1_2) + (1623021/500000000000 : ℝ)*(sp_s1_1) + (8452717/1000000000000 : ℝ)*(sp_s1_2) + (4092443/200000000000 : ℝ)*(sp_s1_7) + (6870935116529/1000000000000 : ℝ)*(sp_s1_14) + (3435476023309/500000000000 : ℝ)*(sp_s1_15) + (3435473563013/500000000000 : ℝ)*(sp_s1_16) + (2402575544801/1000000000000 : ℝ)*(sp_s1_20) + (286083/1000000000000 : ℝ)*(sp_s1_22) + (25001023/1000000000000 : ℝ)*(sp_s1_27) + (96104021833/40000000000 : ℝ)*(f.failure) + (6870955578743/1000000000000 : ℝ)*(f.sum) + (277964740031377602171/488925242900000000000000000000000 : ℝ)*base63 + (59408818210279/864962500000000000000000000 : ℝ)*base64 + (2749597968402439/7065700000000000000000000000 : ℝ)*base66 + (3213138355931897/3459850000000000000000000000 : ℝ)*base69 + (5675968909433037461/122127515225000000000000000000000 : ℝ)*base70 + (955413353974077/1764925000000000000000000000 : ℝ)*base73 + (6399380567138799/7065700000000000000000000000 : ℝ)*base75 + (82806084271617/141194000000000000000000000 : ℝ)*base77 + (149489158619986521617/498817222900000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (267/400000000000000 : ℝ)*base87 + (267/400000000000000 : ℝ)*base89 + (267/400000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10287/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10287/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (37203991922300677981791605788917/3451665537301130000000000000000000000 : ℝ) := by norm_num
    linear_combination (99933018723/500000000000 : ℝ)*(base40) + (760861/200000000000 : ℝ)*(base49) + (30093971131/125000000000 : ℝ)*(base59) + (835644407179/200000000000 : ℝ)*(major_s1_0) + (835644407179/200000000000 : ℝ)*(major_s1_1) + (835644407179/200000000000 : ℝ)*(major_s1_2) + (20182407/1000000000000 : ℝ)*(sp_s1_0) + (17220187/500000000000 : ℝ)*(sp_s1_2) + (23123679/1000000000000 : ℝ)*(sp_s1_16) + (1763933/12500000000 : ℝ)*(sp_s1_20) + (6191426236781/1000000000000 : ℝ)*(sp_s1_21) + (6191446419187/1000000000000 : ℝ)*(sp_s1_22) + (3095694427567/500000000000 : ℝ)*(sp_s1_23) + (1082426472551/500000000000 : ℝ)*(sp_s1_27) + (1082497029871/500000000000 : ℝ)*(f.failure) + (6191446419187/1000000000000 : ℝ)*(f.sum) + (24839884574339939667/97785048580000000000000000000000 : ℝ)*base62 + (39995329265447/69197000000000000000000000 : ℝ)*base64 + (1356441573985571/1413140000000000000000000000 : ℝ)*base66 + (22343823020243/43248125000000000000000000 : ℝ)*base68 + (12561988967142719091/24425503045000000000000000000000 : ℝ)*base71 + (230134598503673/352985000000000000000000000 : ℝ)*base72 + (735892159366461/1413140000000000000000000000 : ℝ)*base74 + (93685109153329/705970000000000000000000000 : ℝ)*base77 + (69494362150652897009/99763444580000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (5429/5000000000000000 : ℝ)*base87 + (5429/5000000000000000 : ℝ)*base89 + (5429/5000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((70597/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(70597/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70657/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70657/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69197/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(69197/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18309/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18309/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43269/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43269/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10287/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10287/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c322053_s1 p hpa hpb X hX hprev0

#print axioms solution

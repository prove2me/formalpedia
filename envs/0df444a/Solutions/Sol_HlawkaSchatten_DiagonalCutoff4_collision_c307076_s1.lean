-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307076_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:17:02.079505+00:00
-- url     : https://prove2.me/submissions/0b2f5b12-8ddc-46d8-a312-1879f109772b

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
theorem collision_support_c307076_s1_s1_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-69592099/500000000 : ℝ)*x 0 + (-1281854321/2000000000 : ℝ)*x 1 + (289290511/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69592099/500000000 : ℝ)^17 ≤ (758715822289/10000000000000 : ℝ)^13 := by
    have hnat : (69592099 : ℕ)^17*10000000000000^13 ≤ 758715822289^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69592099 500000000 758715822289 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1281854321/2000000000 : ℝ)^17 ≤ (27947000072783/50000000000000 : ℝ)^13 := by
    have hnat : (1281854321 : ℕ)^17*50000000000000^13 ≤ 27947000072783^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281854321 2000000000 27947000072783 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (289290511/625000000 : ℝ)^17 ≤ (36518841617399/100000000000000 : ℝ)^13 := by
    have hnat : (289290511 : ℕ)^17*100000000000000^13 ≤ 36518841617399^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289290511 625000000 36518841617399 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69592099/500000000 : ℝ), (-1281854321/2000000000 : ℝ), (289290511/625000000 : ℝ)] ![(758715822289/10000000000000 : ℝ), (27947000072783/50000000000000 : ℝ), (36518841617399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69592099/500000000 : ℝ)|^17 ≤ (758715822289/10000000000000 : ℝ)^13
        have hw : |(-69592099/500000000 : ℝ)|=(69592099/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1281854321/2000000000 : ℝ)|^17 ≤ (27947000072783/50000000000000 : ℝ)^13
        have hw : |(-1281854321/2000000000 : ℝ)|=(1281854321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(289290511/625000000 : ℝ)|^17 ≤ (36518841617399/100000000000000 : ℝ)^13
        have hw : |(289290511/625000000 : ℝ)|=(289290511/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307076_s1_s1_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3287235223/5000000000 : ℝ)*x 0 + (203514389/625000000 : ℝ)*x 1 + (706581477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3287235223/5000000000 : ℝ)^17 ≤ (14446343874577/25000000000000 : ℝ)^13 := by
    have hnat : (3287235223 : ℕ)^17*25000000000000^13 ≤ 14446343874577^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3287235223 5000000000 14446343874577 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203514389/625000000 : ℝ)^17 ≤ (23055857996721/100000000000000 : ℝ)^13 := by
    have hnat : (203514389 : ℕ)^17*100000000000000^13 ≤ 23055857996721^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203514389 625000000 23055857996721 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (706581477/2500000000 : ℝ)^17 ≤ (19158766482953/100000000000000 : ℝ)^13 := by
    have hnat : (706581477 : ℕ)^17*100000000000000^13 ≤ 19158766482953^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706581477 2500000000 19158766482953 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3287235223/5000000000 : ℝ), (203514389/625000000 : ℝ), (706581477/2500000000 : ℝ)] ![(14446343874577/25000000000000 : ℝ), (23055857996721/100000000000000 : ℝ), (19158766482953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3287235223/5000000000 : ℝ)|^17 ≤ (14446343874577/25000000000000 : ℝ)^13
        have hw : |(3287235223/5000000000 : ℝ)|=(3287235223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(203514389/625000000 : ℝ)|^17 ≤ (23055857996721/100000000000000 : ℝ)^13
        have hw : |(203514389/625000000 : ℝ)|=(203514389/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(706581477/2500000000 : ℝ)|^17 ≤ (19158766482953/100000000000000 : ℝ)^13
        have hw : |(706581477/2500000000 : ℝ)|=(706581477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307076_s1_s1_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-140990449/1250000000 : ℝ)*x 0 + (-3817087401/5000000000 : ℝ)*x 1 + (671110489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140990449/1250000000 : ℝ)^17 ≤ (5763329218259/100000000000000 : ℝ)^13 := by
    have hnat : (140990449 : ℕ)^17*100000000000000^13 ≤ 5763329218259^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140990449 1250000000 5763329218259 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3817087401/5000000000 : ℝ)^17 ≤ (17564221631197/25000000000000 : ℝ)^13 := by
    have hnat : (3817087401 : ℕ)^17*25000000000000^13 ≤ 17564221631197^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3817087401 5000000000 17564221631197 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (671110489/2000000000 : ℝ)^17 ≤ (4795956848417/20000000000000 : ℝ)^13 := by
    have hnat : (671110489 : ℕ)^17*20000000000000^13 ≤ 4795956848417^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671110489 2000000000 4795956848417 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-140990449/1250000000 : ℝ), (-3817087401/5000000000 : ℝ), (671110489/2000000000 : ℝ)] ![(5763329218259/100000000000000 : ℝ), (17564221631197/25000000000000 : ℝ), (4795956848417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-140990449/1250000000 : ℝ)|^17 ≤ (5763329218259/100000000000000 : ℝ)^13
        have hw : |(-140990449/1250000000 : ℝ)|=(140990449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3817087401/5000000000 : ℝ)|^17 ≤ (17564221631197/25000000000000 : ℝ)^13
        have hw : |(-3817087401/5000000000 : ℝ)|=(3817087401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(671110489/2000000000 : ℝ)|^17 ≤ (4795956848417/20000000000000 : ℝ)^13
        have hw : |(671110489/2000000000 : ℝ)|=(671110489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307076_s1_s1_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1310569529/2500000000 : ℝ)*x 0 + (4701434153/10000000000 : ℝ)*x 1 + (2893134309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310569529/2500000000 : ℝ)^17 ≤ (2685953898799/6250000000000 : ℝ)^13 := by
    have hnat : (1310569529 : ℕ)^17*6250000000000^13 ≤ 2685953898799^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310569529 2500000000 2685953898799 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4701434153/10000000000 : ℝ)^17 ≤ (18635805307963/50000000000000 : ℝ)^13 := by
    have hnat : (4701434153 : ℕ)^17*50000000000000^13 ≤ 18635805307963^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4701434153 10000000000 18635805307963 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2893134309/10000000000 : ℝ)^17 ≤ (9876563493257/50000000000000 : ℝ)^13 := by
    have hnat : (2893134309 : ℕ)^17*50000000000000^13 ≤ 9876563493257^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2893134309 10000000000 9876563493257 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310569529/2500000000 : ℝ), (4701434153/10000000000 : ℝ), (2893134309/10000000000 : ℝ)] ![(2685953898799/6250000000000 : ℝ), (18635805307963/50000000000000 : ℝ), (9876563493257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310569529/2500000000 : ℝ)|^17 ≤ (2685953898799/6250000000000 : ℝ)^13
        have hw : |(1310569529/2500000000 : ℝ)|=(1310569529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4701434153/10000000000 : ℝ)|^17 ≤ (18635805307963/50000000000000 : ℝ)^13
        have hw : |(4701434153/10000000000 : ℝ)|=(4701434153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2893134309/10000000000 : ℝ)|^17 ≤ (9876563493257/50000000000000 : ℝ)^13
        have hw : |(2893134309/10000000000 : ℝ)|=(2893134309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307076_s1_s1_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (705392047/1250000000 : ℝ)*x 0 + (-1378576441/2500000000 : ℝ)*x 1 + (-637360021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (705392047/1250000000 : ℝ)^17 ≤ (47322243859149/100000000000000 : ℝ)^13 := by
    have hnat : (705392047 : ℕ)^17*100000000000000^13 ≤ 47322243859149^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      705392047 1250000000 47322243859149 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1378576441/2500000000 : ℝ)^17 ≤ (9182893774737/20000000000000 : ℝ)^13 := by
    have hnat : (1378576441 : ℕ)^17*20000000000000^13 ≤ 9182893774737^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378576441 2500000000 9182893774737 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637360021/5000000000 : ℝ)^17 ≤ (6763287261099/100000000000000 : ℝ)^13 := by
    have hnat : (637360021 : ℕ)^17*100000000000000^13 ≤ 6763287261099^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637360021 5000000000 6763287261099 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(705392047/1250000000 : ℝ), (-1378576441/2500000000 : ℝ), (-637360021/5000000000 : ℝ)] ![(47322243859149/100000000000000 : ℝ), (9182893774737/20000000000000 : ℝ), (6763287261099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(705392047/1250000000 : ℝ)|^17 ≤ (47322243859149/100000000000000 : ℝ)^13
        have hw : |(705392047/1250000000 : ℝ)|=(705392047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1378576441/2500000000 : ℝ)|^17 ≤ (9182893774737/20000000000000 : ℝ)^13
        have hw : |(-1378576441/2500000000 : ℝ)|=(1378576441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-637360021/5000000000 : ℝ)|^17 ≤ (6763287261099/100000000000000 : ℝ)^13
        have hw : |(-637360021/5000000000 : ℝ)|=(637360021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307076_s1_s1_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3177117747/10000000000 : ℝ)*x 0 + (44954499/5000000000 : ℝ)*x 1 + (8226015419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3177117747/10000000000 : ℝ)^17 ≤ (22326096144453/100000000000000 : ℝ)^13 := by
    have hnat : (3177117747 : ℕ)^17*100000000000000^13 ≤ 22326096144453^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3177117747 10000000000 22326096144453 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44954499/5000000000 : ℝ)^17 ≤ (13185121817/6250000000000 : ℝ)^13 := by
    have hnat : (44954499 : ℕ)^17*6250000000000^13 ≤ 13185121817^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44954499 5000000000 13185121817 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8226015419/10000000000 : ℝ)^17 ≤ (9682867737693/12500000000000 : ℝ)^13 := by
    have hnat : (8226015419 : ℕ)^17*12500000000000^13 ≤ 9682867737693^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8226015419 10000000000 9682867737693 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3177117747/10000000000 : ℝ), (44954499/5000000000 : ℝ), (8226015419/10000000000 : ℝ)] ![(22326096144453/100000000000000 : ℝ), (13185121817/6250000000000 : ℝ), (9682867737693/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3177117747/10000000000 : ℝ)|^17 ≤ (22326096144453/100000000000000 : ℝ)^13
        have hw : |(3177117747/10000000000 : ℝ)|=(3177117747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44954499/5000000000 : ℝ)|^17 ≤ (13185121817/6250000000000 : ℝ)^13
        have hw : |(44954499/5000000000 : ℝ)|=(44954499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8226015419/10000000000 : ℝ)|^17 ≤ (9682867737693/12500000000000 : ℝ)^13
        have hw : |(8226015419/10000000000 : ℝ)|=(8226015419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307076_s1_s1_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-605339607/5000000000 : ℝ)*x 0 + (-2141942739/5000000000 : ℝ)*x 1 + (3412183473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (605339607/5000000000 : ℝ)^17 ≤ (3161216163793/50000000000000 : ℝ)^13 := by
    have hnat : (605339607 : ℕ)^17*50000000000000^13 ≤ 3161216163793^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605339607 5000000000 3161216163793 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2141942739/5000000000 : ℝ)^17 ≤ (33003286642237/100000000000000 : ℝ)^13 := by
    have hnat : (2141942739 : ℕ)^17*100000000000000^13 ≤ 33003286642237^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141942739 5000000000 33003286642237 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3412183473/5000000000 : ℝ)^17 ≤ (60674281020691/100000000000000 : ℝ)^13 := by
    have hnat : (3412183473 : ℕ)^17*100000000000000^13 ≤ 60674281020691^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3412183473 5000000000 60674281020691 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-605339607/5000000000 : ℝ), (-2141942739/5000000000 : ℝ), (3412183473/5000000000 : ℝ)] ![(3161216163793/50000000000000 : ℝ), (33003286642237/100000000000000 : ℝ), (60674281020691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-605339607/5000000000 : ℝ)|^17 ≤ (3161216163793/50000000000000 : ℝ)^13
        have hw : |(-605339607/5000000000 : ℝ)|=(605339607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2141942739/5000000000 : ℝ)|^17 ≤ (33003286642237/100000000000000 : ℝ)^13
        have hw : |(-2141942739/5000000000 : ℝ)|=(2141942739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3412183473/5000000000 : ℝ)|^17 ≤ (60674281020691/100000000000000 : ℝ)^13
        have hw : |(3412183473/5000000000 : ℝ)|=(3412183473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307076_s1_s1_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7731405267/10000000000 : ℝ)*x 0 + (627434811/2500000000 : ℝ)*x 1 + (998731013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7731405267/10000000000 : ℝ)^17 ≤ (35714652131329/50000000000000 : ℝ)^13 := by
    have hnat : (7731405267 : ℕ)^17*50000000000000^13 ≤ 35714652131329^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7731405267 10000000000 35714652131329 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627434811/2500000000 : ℝ)^17 ≤ (2050260069933/12500000000000 : ℝ)^13 := by
    have hnat : (627434811 : ℕ)^17*12500000000000^13 ≤ 2050260069933^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627434811 2500000000 2050260069933 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998731013/5000000000 : ℝ)^17 ≤ (12168615167523/100000000000000 : ℝ)^13 := by
    have hnat : (998731013 : ℕ)^17*100000000000000^13 ≤ 12168615167523^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998731013 5000000000 12168615167523 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7731405267/10000000000 : ℝ), (627434811/2500000000 : ℝ), (998731013/5000000000 : ℝ)] ![(35714652131329/50000000000000 : ℝ), (2050260069933/12500000000000 : ℝ), (12168615167523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7731405267/10000000000 : ℝ)|^17 ≤ (35714652131329/50000000000000 : ℝ)^13
        have hw : |(7731405267/10000000000 : ℝ)|=(7731405267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(627434811/2500000000 : ℝ)|^17 ≤ (2050260069933/12500000000000 : ℝ)^13
        have hw : |(627434811/2500000000 : ℝ)|=(627434811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(998731013/5000000000 : ℝ)|^17 ≤ (12168615167523/100000000000000 : ℝ)^13
        have hw : |(998731013/5000000000 : ℝ)|=(998731013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307076_s1_s1_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (18267317/39062500 : ℝ)*x 0 + (-6002740023/10000000000 : ℝ)*x 1 + (-968143697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18267317/39062500 : ℝ)^17 ≤ (37012637379707/100000000000000 : ℝ)^13 := by
    have hnat : (18267317 : ℕ)^17*100000000000000^13 ≤ 37012637379707^13*39062500^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18267317 39062500 37012637379707 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6002740023/10000000000 : ℝ)^17 ≤ (10260756633373/20000000000000 : ℝ)^13 := by
    have hnat : (6002740023 : ℕ)^17*20000000000000^13 ≤ 10260756633373^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6002740023 10000000000 10260756633373 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (968143697/5000000000 : ℝ)^17 ≤ (5841789721303/50000000000000 : ℝ)^13 := by
    have hnat : (968143697 : ℕ)^17*50000000000000^13 ≤ 5841789721303^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968143697 5000000000 5841789721303 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(18267317/39062500 : ℝ), (-6002740023/10000000000 : ℝ), (-968143697/5000000000 : ℝ)] ![(37012637379707/100000000000000 : ℝ), (10260756633373/20000000000000 : ℝ), (5841789721303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(18267317/39062500 : ℝ)|^17 ≤ (37012637379707/100000000000000 : ℝ)^13
        have hw : |(18267317/39062500 : ℝ)|=(18267317/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6002740023/10000000000 : ℝ)|^17 ≤ (10260756633373/20000000000000 : ℝ)^13
        have hw : |(-6002740023/10000000000 : ℝ)|=(6002740023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-968143697/5000000000 : ℝ)|^17 ≤ (5841789721303/50000000000000 : ℝ)^13
        have hw : |(-968143697/5000000000 : ℝ)|=(968143697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307076_s1_s1_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6145151/31250000 : ℝ)*x 0 + (-9669/1000000000 : ℝ)*x 1 + (9074844491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6145151/31250000 : ℝ)^17 ≤ (2980534106411/25000000000000 : ℝ)^13 := by
    have hnat : (6145151 : ℕ)^17*25000000000000^13 ≤ 2980534106411^13*31250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6145151 31250000 2980534106411 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9669/1000000000 : ℝ)^17 ≤ (27696319/100000000000000 : ℝ)^13 := by
    have hnat : (9669 : ℕ)^17*100000000000000^13 ≤ 27696319^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9669 1000000000 27696319 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9074844491/10000000000 : ℝ)^17 ≤ (22019458965089/25000000000000 : ℝ)^13 := by
    have hnat : (9074844491 : ℕ)^17*25000000000000^13 ≤ 22019458965089^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9074844491 10000000000 22019458965089 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6145151/31250000 : ℝ), (-9669/1000000000 : ℝ), (9074844491/10000000000 : ℝ)] ![(2980534106411/25000000000000 : ℝ), (27696319/100000000000000 : ℝ), (22019458965089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6145151/31250000 : ℝ)|^17 ≤ (2980534106411/25000000000000 : ℝ)^13
        have hw : |(6145151/31250000 : ℝ)|=(6145151/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9669/1000000000 : ℝ)|^17 ≤ (27696319/100000000000000 : ℝ)^13
        have hw : |(-9669/1000000000 : ℝ)|=(9669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9074844491/10000000000 : ℝ)|^17 ≤ (22019458965089/25000000000000 : ℝ)^13
        have hw : |(9074844491/10000000000 : ℝ)|=(9074844491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307076_s1_s1_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-63456193/1250000000 : ℝ)*x 0 + (-7725009189/10000000000 : ℝ)*x 1 + (3634465913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63456193/1250000000 : ℝ)^17 ≤ (2028971751307/100000000000000 : ℝ)^13 := by
    have hnat : (63456193 : ℕ)^17*100000000000000^13 ≤ 2028971751307^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63456193 1250000000 2028971751307 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7725009189/10000000000 : ℝ)^17 ≤ (8919004925537/12500000000000 : ℝ)^13 := by
    have hnat : (7725009189 : ℕ)^17*12500000000000^13 ≤ 8919004925537^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7725009189 10000000000 8919004925537 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3634465913/10000000000 : ℝ)^17 ≤ (13309494412067/50000000000000 : ℝ)^13 := by
    have hnat : (3634465913 : ℕ)^17*50000000000000^13 ≤ 13309494412067^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3634465913 10000000000 13309494412067 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63456193/1250000000 : ℝ), (-7725009189/10000000000 : ℝ), (3634465913/10000000000 : ℝ)] ![(2028971751307/100000000000000 : ℝ), (8919004925537/12500000000000 : ℝ), (13309494412067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63456193/1250000000 : ℝ)|^17 ≤ (2028971751307/100000000000000 : ℝ)^13
        have hw : |(-63456193/1250000000 : ℝ)|=(63456193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7725009189/10000000000 : ℝ)|^17 ≤ (8919004925537/12500000000000 : ℝ)^13
        have hw : |(-7725009189/10000000000 : ℝ)|=(7725009189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3634465913/10000000000 : ℝ)|^17 ≤ (13309494412067/50000000000000 : ℝ)^13
        have hw : |(3634465913/10000000000 : ℝ)|=(3634465913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307076_s1_s1_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (963319921/1250000000 : ℝ)*x 0 + (1255456373/5000000000 : ℝ)*x 1 + (1016881623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (963319921/1250000000 : ℝ)^17 ≤ (71129275192747/100000000000000 : ℝ)^13 := by
    have hnat : (963319921 : ℕ)^17*100000000000000^13 ≤ 71129275192747^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963319921 1250000000 71129275192747 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1255456373/5000000000 : ℝ)^17 ≤ (16412110329573/100000000000000 : ℝ)^13 := by
    have hnat : (1255456373 : ℕ)^17*100000000000000^13 ≤ 16412110329573^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255456373 5000000000 16412110329573 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016881623/5000000000 : ℝ)^17 ≤ (1557326808183/12500000000000 : ℝ)^13 := by
    have hnat : (1016881623 : ℕ)^17*12500000000000^13 ≤ 1557326808183^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016881623 5000000000 1557326808183 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(963319921/1250000000 : ℝ), (1255456373/5000000000 : ℝ), (1016881623/5000000000 : ℝ)] ![(71129275192747/100000000000000 : ℝ), (16412110329573/100000000000000 : ℝ), (1557326808183/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(963319921/1250000000 : ℝ)|^17 ≤ (71129275192747/100000000000000 : ℝ)^13
        have hw : |(963319921/1250000000 : ℝ)|=(963319921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1255456373/5000000000 : ℝ)|^17 ≤ (16412110329573/100000000000000 : ℝ)^13
        have hw : |(1255456373/5000000000 : ℝ)|=(1255456373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016881623/5000000000 : ℝ)|^17 ≤ (1557326808183/12500000000000 : ℝ)^13
        have hw : |(1016881623/5000000000 : ℝ)|=(1016881623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307076_s1_s1_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1748902359/5000000000 : ℝ)*x 0 + (-33315817/50000000 : ℝ)*x 1 + (-1223935577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1748902359/5000000000 : ℝ)^17 ≤ (6329435385831/25000000000000 : ℝ)^13 := by
    have hnat : (1748902359 : ℕ)^17*25000000000000^13 ≤ 6329435385831^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748902359 5000000000 6329435385831 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33315817/50000000 : ℝ)^17 ≤ (58806901662573/100000000000000 : ℝ)^13 := by
    have hnat : (33315817 : ℕ)^17*100000000000000^13 ≤ 58806901662573^13*50000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33315817 50000000 58806901662573 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1223935577/5000000000 : ℝ)^17 ≤ (7937678392089/50000000000000 : ℝ)^13 := by
    have hnat : (1223935577 : ℕ)^17*50000000000000^13 ≤ 7937678392089^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223935577 5000000000 7937678392089 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1748902359/5000000000 : ℝ), (-33315817/50000000 : ℝ), (-1223935577/5000000000 : ℝ)] ![(6329435385831/25000000000000 : ℝ), (58806901662573/100000000000000 : ℝ), (7937678392089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1748902359/5000000000 : ℝ)|^17 ≤ (6329435385831/25000000000000 : ℝ)^13
        have hw : |(1748902359/5000000000 : ℝ)|=(1748902359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33315817/50000000 : ℝ)|^17 ≤ (58806901662573/100000000000000 : ℝ)^13
        have hw : |(-33315817/50000000 : ℝ)|=(33315817/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1223935577/5000000000 : ℝ)|^17 ≤ (7937678392089/50000000000000 : ℝ)^13
        have hw : |(-1223935577/5000000000 : ℝ)|=(1223935577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307076_s1_s1_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6406465017/10000000000 : ℝ)*x 0 + (457647/1250000000 : ℝ)*x 1 + (1070020337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6406465017/10000000000 : ℝ)^17 ≤ (55861995613113/100000000000000 : ℝ)^13 := by
    have hnat : (6406465017 : ℕ)^17*100000000000000^13 ≤ 55861995613113^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6406465017 10000000000 55861995613113 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (457647/1250000000 : ℝ)^17 ≤ (641657237/20000000000000 : ℝ)^13 := by
    have hnat : (457647 : ℕ)^17*20000000000000^13 ≤ 641657237^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457647 1250000000 641657237 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1070020337/2000000000 : ℝ)^17 ≤ (8826959219617/20000000000000 : ℝ)^13 := by
    have hnat : (1070020337 : ℕ)^17*20000000000000^13 ≤ 8826959219617^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070020337 2000000000 8826959219617 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6406465017/10000000000 : ℝ), (457647/1250000000 : ℝ), (1070020337/2000000000 : ℝ)] ![(55861995613113/100000000000000 : ℝ), (641657237/20000000000000 : ℝ), (8826959219617/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6406465017/10000000000 : ℝ)|^17 ≤ (55861995613113/100000000000000 : ℝ)^13
        have hw : |(6406465017/10000000000 : ℝ)|=(6406465017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(457647/1250000000 : ℝ)|^17 ≤ (641657237/20000000000000 : ℝ)^13
        have hw : |(457647/1250000000 : ℝ)|=(457647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1070020337/2000000000 : ℝ)|^17 ≤ (8826959219617/20000000000000 : ℝ)^13
        have hw : |(1070020337/2000000000 : ℝ)|=(1070020337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307076_s1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((17463/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17463/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-89791/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-89791/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(93899/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(93899/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((70901/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(70901/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-14911/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-14911/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79371/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79371/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (92559/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s1_pow0 : (17463/20000 : ℝ) ^ (135/32 : ℝ) ≤ (56424617165794635671/100000000000000000000 : ℝ) := by
    have hpowers : (17463/20000 : ℝ)^135 ≤ (56424617165794635671/100000000000000000000 : ℝ)^32 := by
      have hnat : (17463 : ℕ)^135*100000000000000000000^32 ≤ 56424617165794635671^32*20000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17463 20000 56424617165794635671 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17463/20000 : ℝ)) (X := (56424617165794635671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (156424617165794635671/100000000000000000000 : ℝ) ≤ (1389848678165417/1250000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (156424617165794635671/100000000000000000000 : ℝ)^32 ≤ (1389848678165417/1250000000000000 : ℝ)^135 := by
      have hnat : (156424617165794635671 : ℕ)^32*1250000000000000^135 ≤ 1389848678165417^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        156424617165794635671 100000000000000000000 1389848678165417 1250000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1389848678165417/1250000000000000 : ℝ)) (X := (156424617165794635671/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (106424617165794635671/50000000000000000000 : ℝ) ≤ (11960937930544521/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (106424617165794635671/50000000000000000000 : ℝ)^32 ≤ (11960937930544521/10000000000000000 : ℝ)^135 := by
      have hnat : (106424617165794635671 : ℕ)^32*10000000000000000^135 ≤ 11960937930544521^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106424617165794635671 50000000000000000000 11960937930544521 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11960937930544521/10000000000000000 : ℝ)) (X := (106424617165794635671/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(46616226055139/363812500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(168429701044237/1746300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (17463/20000 : ℝ)) (alpha := (46616226055139/363812500000000 : ℝ)) (beta := (168429701044237/1746300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (17463/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(46616226055139/363812500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(168429701044237/1746300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (89791/100000 : ℝ) ^ (135/32 : ℝ) ≤ (63489354276495513537/100000000000000000000 : ℝ) := by
    have hpowers : (89791/100000 : ℝ)^135 ≤ (63489354276495513537/100000000000000000000 : ℝ)^32 := by
      have hnat : (89791 : ℕ)^135*100000000000000000000^32 ≤ 63489354276495513537^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89791 100000 63489354276495513537 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89791/100000 : ℝ)) (X := (63489354276495513537/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (163489354276495513537/100000000000000000000 : ℝ) ≤ (2247164726081431/2000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (163489354276495513537/100000000000000000000 : ℝ)^32 ≤ (2247164726081431/2000000000000000 : ℝ)^135 := by
      have hnat : (163489354276495513537 : ℕ)^32*2000000000000000^135 ≤ 2247164726081431^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        163489354276495513537 100000000000000000000 2247164726081431 2000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2247164726081431/2000000000000000 : ℝ)) (X := (163489354276495513537/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (113489354276495513537/50000000000000000000 : ℝ) ≤ (3036139114856133/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (113489354276495513537/50000000000000000000 : ℝ)^32 ≤ (3036139114856133/2500000000000000 : ℝ)^135 := by
      have hnat : (113489354276495513537 : ℕ)^32*2500000000000000^135 ≤ 3036139114856133^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113489354276495513537 50000000000000000000 3036139114856133 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3036139114856133/2500000000000000 : ℝ)) (X := (113489354276495513537/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(247164726081431/1795820000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(69902525309029/690700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (89791/100000 : ℝ)) (alpha := (247164726081431/1795820000000000 : ℝ)) (beta := (69902525309029/690700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (89791/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(247164726081431/1795820000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(69902525309029/690700000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (93899/100000 : ℝ) ^ (135/32 : ℝ) ≤ (76676707367111471179/100000000000000000000 : ℝ) := by
    have hpowers : (93899/100000 : ℝ)^135 ≤ (76676707367111471179/100000000000000000000 : ℝ)^32 := by
      have hnat : (93899 : ℕ)^135*100000000000000000000^32 ≤ 76676707367111471179^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93899 100000 76676707367111471179 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (93899/100000 : ℝ)) (X := (76676707367111471179/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (176676707367111471179/100000000000000000000 : ℝ) ≤ (2288867453888903/2000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (176676707367111471179/100000000000000000000 : ℝ)^32 ≤ (2288867453888903/2000000000000000 : ℝ)^135 := by
      have hnat : (176676707367111471179 : ℕ)^32*2000000000000000^135 ≤ 2288867453888903^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        176676707367111471179 100000000000000000000 2288867453888903 2000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2288867453888903/2000000000000000 : ℝ)) (X := (176676707367111471179/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (126676707367111471179/50000000000000000000 : ℝ) ≤ (311629242597699/250000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (126676707367111471179/50000000000000000000 : ℝ)^32 ≤ (311629242597699/250000000000000 : ℝ)^135 := by
      have hnat : (126676707367111471179 : ℕ)^32*250000000000000^135 ≤ 311629242597699^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        126676707367111471179 50000000000000000000 311629242597699 250000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (311629242597699/250000000000000 : ℝ)) (X := (126676707367111471179/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(288867453888903/1877980000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(204166486892689/1877980000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (93899/100000 : ℝ)) (alpha := (288867453888903/1877980000000000 : ℝ)) (beta := (204166486892689/1877980000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (93899/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(288867453888903/1877980000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(204166486892689/1877980000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-69592099/500000000 : ℝ)*X 0 0+(-1281854321/2000000000 : ℝ)*X 0 1+(289290511/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307076_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3287235223/5000000000 : ℝ)*X 1 0+(203514389/625000000 : ℝ)*X 1 1+(706581477/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307076_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-140990449/1250000000 : ℝ)*X 0 0+(-3817087401/5000000000 : ℝ)*X 0 1+(671110489/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307076_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1310569529/2500000000 : ℝ)*X 1 0+(4701434153/10000000000 : ℝ)*X 1 1+(2893134309/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307076_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((705392047/1250000000 : ℝ)*X 2 0+(-1378576441/2500000000 : ℝ)*X 2 1+(-637360021/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307076_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((3177117747/10000000000 : ℝ)*X 0 0+(44954499/5000000000 : ℝ)*X 0 1+(8226015419/10000000000 : ℝ)*X 0 2+(3177117747/10000000000 : ℝ)*X 1 0+(44954499/5000000000 : ℝ)*X 1 1+(8226015419/10000000000 : ℝ)*X 1 2+(3177117747/10000000000 : ℝ)*X 2 0+(44954499/5000000000 : ℝ)*X 2 1+(8226015419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307076_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-605339607/5000000000 : ℝ)*X 0 0+(-2141942739/5000000000 : ℝ)*X 0 1+(3412183473/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307076_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((7731405267/10000000000 : ℝ)*X 1 0+(627434811/2500000000 : ℝ)*X 1 1+(998731013/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307076_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((18267317/39062500 : ℝ)*X 2 0+(-6002740023/10000000000 : ℝ)*X 2 1+(-968143697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307076_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((6145151/31250000 : ℝ)*X 0 0+(-9669/1000000000 : ℝ)*X 0 1+(9074844491/10000000000 : ℝ)*X 0 2+(6145151/31250000 : ℝ)*X 1 0+(-9669/1000000000 : ℝ)*X 1 1+(9074844491/10000000000 : ℝ)*X 1 2+(6145151/31250000 : ℝ)*X 2 0+(-9669/1000000000 : ℝ)*X 2 1+(9074844491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307076_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-63456193/1250000000 : ℝ)*X 0 0+(-7725009189/10000000000 : ℝ)*X 0 1+(3634465913/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307076_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((963319921/1250000000 : ℝ)*X 1 0+(1255456373/5000000000 : ℝ)*X 1 1+(1016881623/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307076_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1748902359/5000000000 : ℝ)*X 2 0+(-33315817/50000000 : ℝ)*X 2 1+(-1223935577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307076_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((6406465017/10000000000 : ℝ)*X 0 0+(457647/1250000000 : ℝ)*X 0 1+(1070020337/2000000000 : ℝ)*X 0 2+(6406465017/10000000000 : ℝ)*X 1 0+(457647/1250000000 : ℝ)*X 1 1+(1070020337/2000000000 : ℝ)*X 1 2+(6406465017/10000000000 : ℝ)*X 2 0+(457647/1250000000 : ℝ)*X 2 1+(1070020337/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307076_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((70901/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(70901/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1177808928661418255475666985529/94381751191325000000000000000000000 : ℝ) := by norm_num
    linear_combination (16361585833/125000000000 : ℝ)*(base3) + (63886651313/125000000000 : ℝ)*(base7) + (2238471/1000000000000 : ℝ)*(base40) + (467729709047/500000000000 : ℝ)*(base54) + (2433834660917/1000000000000 : ℝ)*(major_s1_0) + (2433834660917/1000000000000 : ℝ)*(major_s1_1) + (1498375242823/1000000000000 : ℝ)*(major_s1_2) + (1946719/1000000000000 : ℝ)*(sp_s1_0) + (2986597479409/1000000000000 : ℝ)*(sp_s1_7) + (3117492112793/1000000000000 : ℝ)*(sp_s1_8) + (2051092337941/1000000000000 : ℝ)*(sp_s1_9) + (101043082913/100000000000 : ℝ)*(sp_s1_13) + (47670093/1000000000000 : ℝ)*(sp_s1_16) + (418053/500000000000 : ℝ)*(sp_s1_20) + (1565690559491/1000000000000 : ℝ)*(f.failure) + (2986599426129/1000000000000 : ℝ)*(f.sum) + (93574557557349689/2026751228125000000000000000000 : ℝ)*base63 + (1109514022304379/1877980000000000000000000000 : ℝ)*base64 + (1365445262025397/1795820000000000000000000000 : ℝ)*base67 + (42303557002561/375596000000000000000000000 : ℝ)*base69 + (99115956601105331021/273293039500000000000000000000000 : ℝ)*base71 + (184903503645061/1746300000000000000000000000 : ℝ)*base72 + (450495040333667/690700000000000000000000000 : ℝ)*base75 + (104278370887073/1455250000000000000000000000 : ℝ)*base76 + (3204333448086715427/19600252912500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (7121/12500000000000000 : ℝ)*base87 + (7121/12500000000000000 : ℝ)*base89 + (7121/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-14911/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-14911/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (194606619344567894582680369869/47190875595662500000000000000000000 : ℝ) := by norm_num
    linear_combination (81573/25000000000 : ℝ)*(base3) + (124727809727/200000000000 : ℝ)*(base7) + (592581946587/1000000000000 : ℝ)*(base33) + (4942374509/200000000000 : ℝ)*(base40) + (546971/500000000000 : ℝ)*(base54) + (4000444887/3125000000 : ℝ)*(major_s1_0) + (1872724310427/1000000000000 : ℝ)*(major_s1_1) + (374544643297/200000000000 : ℝ)*(major_s1_2) + (10492947/1000000000000 : ℝ)*(sp_s1_13) + (1077948676269/500000000000 : ℝ)*(sp_s1_14) + (390530414189/250000000000 : ℝ)*(sp_s1_15) + (1563314312009/1000000000000 : ℝ)*(sp_s1_16) + (91417569059/50000000000 : ℝ)*(sp_s1_20) + (239402423/200000000000 : ℝ)*(sp_s1_22) + (240945436471/200000000000 : ℝ)*(f.failure) + (1077948676269/500000000000 : ℝ)*(f.sum) + (4255452182136115499/32428019650000000000000000000000 : ℝ)*base63 + (329998179030049/1877980000000000000000000000 : ℝ)*base65 + (177826559227123/359164000000000000000000000 : ℝ)*base67 + (728471639024517/1877980000000000000000000000 : ℝ)*base69 + (663479145193639691/54658607900000000000000000000000 : ℝ)*base70 + (29378819071637/58210000000000000000000000 : ℝ)*base73 + (89602204115227/690700000000000000000000000 : ℝ)*base75 + (105831693344613/291050000000000000000000000 : ℝ)*base77 + (1304799757535576507/2090693644000000000000000000000 : ℝ)*base79 + (501/2500000000000000 : ℝ)*base87 + (501/2500000000000000 : ℝ)*base89 + (501/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79371/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79371/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (93822531785478322308471367/13066835275000000000000000000000 : ℝ) := by norm_num
    linear_combination (103549922179/200000000000 : ℝ)*(base3) + (855112197073/1000000000000 : ℝ)*(base7) + (268650835483/1000000000000 : ℝ)*(base40) + (651212976863/250000000000 : ℝ)*(major_s1_0) + (651212976863/250000000000 : ℝ)*(major_s1_1) + (651212976863/250000000000 : ℝ)*(major_s1_2) + (2104387/1000000000000 : ℝ)*(sp_s1_0) + (17086587/1000000000000 : ℝ)*(sp_s1_1) + (643869801/1000000000000 : ℝ)*(sp_s1_15) + (5473529/250000000000 : ℝ)*(sp_s1_16) + (375792187349/125000000000 : ℝ)*(sp_s1_21) + (3523428257687/1000000000000 : ℝ)*(sp_s1_22) + (3006317709063/1000000000000 : ℝ)*(sp_s1_23) + (503267218043/250000000000 : ℝ)*(sp_s1_27) + (837853142997/500000000000 : ℝ)*(f.failure) + (3006339603179/1000000000000 : ℝ)*(f.sum) + (2362229833075091061/8107004912500000000000000000000 : ℝ)*base63 + (214055275611563/938990000000000000000000000 : ℝ)*base65 + (74919021968621/448955000000000000000000000 : ℝ)*base66 + (723904426884113/938990000000000000000000000 : ℝ)*base68 + (541615870839776689/17080814968750000000000000000000 : ℝ)*base70 + (275635030631899/436575000000000000000000000 : ℝ)*base72 + (54482029963/43168750000000000000000000 : ℝ)*base74 + (213345707329053/363812500000000000000000000 : ℝ)*base77 + (5595472622943870439/39200505825000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (293/6250000000000000 : ℝ)*base86 + (293/6250000000000000 : ℝ)*base88 + (293/6250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((17463/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17463/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-89791/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-89791/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(93899/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(93899/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((70901/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(70901/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-14911/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-14911/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79371/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79371/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307076_s1 p hpa hpb X hX hprev0

#print axioms solution

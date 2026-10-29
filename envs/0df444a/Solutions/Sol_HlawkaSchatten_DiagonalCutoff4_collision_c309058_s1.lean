-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309058_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:03:53.656665+00:00
-- url     : https://prove2.me/submissions/96ac0d8f-cef9-4b40-ab3c-9cf319d9df68

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
theorem collision_support_c309058_s1_s1_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1561787807/5000000000 : ℝ)*x 0 + (3043499217/10000000000 : ℝ)*x 1 + (-6435726743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1561787807/5000000000 : ℝ)^35 ≤ (11063417309511/50000000000000 : ℝ)^27 := by
    have hnat : (1561787807 : ℕ)^35*50000000000000^27 ≤ 11063417309511^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1561787807 5000000000 11063417309511 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3043499217/10000000000 : ℝ)^35 ≤ (10697162411763/50000000000000 : ℝ)^27 := by
    have hnat : (3043499217 : ℕ)^35*50000000000000^27 ≤ 10697162411763^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3043499217 10000000000 10697162411763 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6435726743/10000000000 : ℝ)^35 ≤ (11295768109523/20000000000000 : ℝ)^27 := by
    have hnat : (6435726743 : ℕ)^35*20000000000000^27 ≤ 11295768109523^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6435726743 10000000000 11295768109523 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1561787807/5000000000 : ℝ), (3043499217/10000000000 : ℝ), (-6435726743/10000000000 : ℝ)] ![(11063417309511/50000000000000 : ℝ), (10697162411763/50000000000000 : ℝ), (11295768109523/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1561787807/5000000000 : ℝ)|^35 ≤ (11063417309511/50000000000000 : ℝ)^27
        have hw : |(-1561787807/5000000000 : ℝ)|=(1561787807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3043499217/10000000000 : ℝ)|^35 ≤ (10697162411763/50000000000000 : ℝ)^27
        have hw : |(3043499217/10000000000 : ℝ)|=(3043499217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6435726743/10000000000 : ℝ)|^35 ≤ (11295768109523/20000000000000 : ℝ)^27
        have hw : |(-6435726743/10000000000 : ℝ)|=(6435726743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309058_s1_s1_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (15996387/50000000 : ℝ)*x 0 + (-3087012241/10000000000 : ℝ)*x 1 + (-3169629761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15996387/50000000 : ℝ)^35 ≤ (4564893022189/20000000000000 : ℝ)^27 := by
    have hnat : (15996387 : ℕ)^35*20000000000000^27 ≤ 4564893022189^27*50000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15996387 50000000 4564893022189 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3087012241/10000000000 : ℝ)^35 ≤ (5447916774879/25000000000000 : ℝ)^27 := by
    have hnat : (3087012241 : ℕ)^35*25000000000000^27 ≤ 5447916774879^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3087012241 10000000000 5447916774879 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3169629761/5000000000 : ℝ)^35 ≤ (11076773555371/20000000000000 : ℝ)^27 := by
    have hnat : (3169629761 : ℕ)^35*20000000000000^27 ≤ 11076773555371^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169629761 5000000000 11076773555371 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(15996387/50000000 : ℝ), (-3087012241/10000000000 : ℝ), (-3169629761/5000000000 : ℝ)] ![(4564893022189/20000000000000 : ℝ), (5447916774879/25000000000000 : ℝ), (11076773555371/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(15996387/50000000 : ℝ)|^35 ≤ (4564893022189/20000000000000 : ℝ)^27
        have hw : |(15996387/50000000 : ℝ)|=(15996387/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3087012241/10000000000 : ℝ)|^35 ≤ (5447916774879/25000000000000 : ℝ)^27
        have hw : |(-3087012241/10000000000 : ℝ)|=(3087012241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3169629761/5000000000 : ℝ)|^35 ≤ (11076773555371/20000000000000 : ℝ)^27
        have hw : |(-3169629761/5000000000 : ℝ)|=(3169629761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309058_s1_s1_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2213498189/10000000000 : ℝ)*x 0 + (422122813/2500000000 : ℝ)*x 1 + (-8081580559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2213498189/10000000000 : ℝ)^35 ≤ (14158868718731/100000000000000 : ℝ)^27 := by
    have hnat : (2213498189 : ℕ)^35*100000000000000^27 ≤ 14158868718731^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213498189 10000000000 14158868718731 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422122813/2500000000 : ℝ)^35 ≤ (1993607094879/20000000000000 : ℝ)^27 := by
    have hnat : (422122813 : ℕ)^35*20000000000000^27 ≤ 1993607094879^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422122813 2500000000 1993607094879 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8081580559/10000000000 : ℝ)^35 ≤ (75873095796221/100000000000000 : ℝ)^27 := by
    have hnat : (8081580559 : ℕ)^35*100000000000000^27 ≤ 75873095796221^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8081580559 10000000000 75873095796221 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2213498189/10000000000 : ℝ), (422122813/2500000000 : ℝ), (-8081580559/10000000000 : ℝ)] ![(14158868718731/100000000000000 : ℝ), (1993607094879/20000000000000 : ℝ), (75873095796221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2213498189/10000000000 : ℝ)|^35 ≤ (14158868718731/100000000000000 : ℝ)^27
        have hw : |(-2213498189/10000000000 : ℝ)|=(2213498189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422122813/2500000000 : ℝ)|^35 ≤ (1993607094879/20000000000000 : ℝ)^27
        have hw : |(422122813/2500000000 : ℝ)|=(422122813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8081580559/10000000000 : ℝ)|^35 ≤ (75873095796221/100000000000000 : ℝ)^27
        have hw : |(-8081580559/10000000000 : ℝ)|=(8081580559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309058_s1_s1_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (74225889/312500000 : ℝ)*x 0 + (-1701296819/10000000000 : ℝ)*x 1 + (-7961891019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (74225889/312500000 : ℝ)^35 ≤ (15514193514377/100000000000000 : ℝ)^27 := by
    have hnat : (74225889 : ℕ)^35*100000000000000^27 ≤ 15514193514377^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74225889 312500000 15514193514377 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1701296819/10000000000 : ℝ)^35 ≤ (201322852537/2000000000000 : ℝ)^27 := by
    have hnat : (1701296819 : ℕ)^35*2000000000000^27 ≤ 201322852537^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1701296819 10000000000 201322852537 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7961891019/10000000000 : ℝ)^35 ≤ (18604915959061/25000000000000 : ℝ)^27 := by
    have hnat : (7961891019 : ℕ)^35*25000000000000^27 ≤ 18604915959061^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7961891019 10000000000 18604915959061 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(74225889/312500000 : ℝ), (-1701296819/10000000000 : ℝ), (-7961891019/10000000000 : ℝ)] ![(15514193514377/100000000000000 : ℝ), (201322852537/2000000000000 : ℝ), (18604915959061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(74225889/312500000 : ℝ)|^35 ≤ (15514193514377/100000000000000 : ℝ)^27
        have hw : |(74225889/312500000 : ℝ)|=(74225889/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1701296819/10000000000 : ℝ)|^35 ≤ (201322852537/2000000000000 : ℝ)^27
        have hw : |(-1701296819/10000000000 : ℝ)|=(1701296819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7961891019/10000000000 : ℝ)|^35 ≤ (18604915959061/25000000000000 : ℝ)^27
        have hw : |(-7961891019/10000000000 : ℝ)|=(7961891019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309058_s1_s1_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (84944191/200000000 : ℝ)*x 0 + (1296598019/2000000000 : ℝ)*x 1 + (1696399453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84944191/200000000 : ℝ)^35 ≤ (16477153728449/50000000000000 : ℝ)^27 := by
    have hnat : (84944191 : ℕ)^35*50000000000000^27 ≤ 16477153728449^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84944191 200000000 16477153728449 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296598019/2000000000 : ℝ)^35 ≤ (7127136996441/12500000000000 : ℝ)^27 := by
    have hnat : (1296598019 : ℕ)^35*12500000000000^27 ≤ 7127136996441^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296598019 2000000000 7127136996441 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1696399453/10000000000 : ℝ)^35 ≤ (5014298279637/50000000000000 : ℝ)^27 := by
    have hnat : (1696399453 : ℕ)^35*50000000000000^27 ≤ 5014298279637^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696399453 10000000000 5014298279637 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84944191/200000000 : ℝ), (1296598019/2000000000 : ℝ), (1696399453/10000000000 : ℝ)] ![(16477153728449/50000000000000 : ℝ), (7127136996441/12500000000000 : ℝ), (5014298279637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84944191/200000000 : ℝ)|^35 ≤ (16477153728449/50000000000000 : ℝ)^27
        have hw : |(84944191/200000000 : ℝ)|=(84944191/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296598019/2000000000 : ℝ)|^35 ≤ (7127136996441/12500000000000 : ℝ)^27
        have hw : |(1296598019/2000000000 : ℝ)|=(1296598019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1696399453/10000000000 : ℝ)|^35 ≤ (5014298279637/50000000000000 : ℝ)^27
        have hw : |(1696399453/10000000000 : ℝ)|=(1696399453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309058_s1_s1_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2617891919/10000000000 : ℝ)*x 0 + (8612852081/10000000000 : ℝ)*x 1 + (-84261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617891919/10000000000 : ℝ)^35 ≤ (17599201376261/100000000000000 : ℝ)^27 := by
    have hnat : (2617891919 : ℕ)^35*100000000000000^27 ≤ 17599201376261^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617891919 10000000000 17599201376261 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8612852081/10000000000 : ℝ)^35 ≤ (82400772186059/100000000000000 : ℝ)^27 := by
    have hnat : (8612852081 : ℕ)^35*100000000000000^27 ≤ 82400772186059^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8612852081 10000000000 82400772186059 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84261/10000000000 : ℝ)^35 ≤ (5286139/20000000000000 : ℝ)^27 := by
    have hnat : (84261 : ℕ)^35*20000000000000^27 ≤ 5286139^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84261 10000000000 5286139 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617891919/10000000000 : ℝ), (8612852081/10000000000 : ℝ), (-84261/10000000000 : ℝ)] ![(17599201376261/100000000000000 : ℝ), (82400772186059/100000000000000 : ℝ), (5286139/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617891919/10000000000 : ℝ)|^35 ≤ (17599201376261/100000000000000 : ℝ)^27
        have hw : |(2617891919/10000000000 : ℝ)|=(2617891919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8612852081/10000000000 : ℝ)|^35 ≤ (82400772186059/100000000000000 : ℝ)^27
        have hw : |(8612852081/10000000000 : ℝ)|=(8612852081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-84261/10000000000 : ℝ)|^35 ≤ (5286139/20000000000000 : ℝ)^27
        have hw : |(-84261/10000000000 : ℝ)|=(84261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309058_s1_s1_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-43434847/200000000 : ℝ)*x 0 + (1246834709/5000000000 : ℝ)*x 1 + (-1513257287/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43434847/200000000 : ℝ)^35 ≤ (6906802863353/50000000000000 : ℝ)^27 := by
    have hnat : (43434847 : ℕ)^35*50000000000000^27 ≤ 6906802863353^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43434847 200000000 6906802863353 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1246834709/5000000000 : ℝ)^35 ≤ (3304870668849/20000000000000 : ℝ)^27 := by
    have hnat : (1246834709 : ℕ)^35*20000000000000^27 ≤ 3304870668849^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246834709 5000000000 3304870668849 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1513257287/2000000000 : ℝ)^35 ≤ (69662040918799/100000000000000 : ℝ)^27 := by
    have hnat : (1513257287 : ℕ)^35*100000000000000^27 ≤ 69662040918799^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1513257287 2000000000 69662040918799 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43434847/200000000 : ℝ), (1246834709/5000000000 : ℝ), (-1513257287/2000000000 : ℝ)] ![(6906802863353/50000000000000 : ℝ), (3304870668849/20000000000000 : ℝ), (69662040918799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43434847/200000000 : ℝ)|^35 ≤ (6906802863353/50000000000000 : ℝ)^27
        have hw : |(-43434847/200000000 : ℝ)|=(43434847/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1246834709/5000000000 : ℝ)|^35 ≤ (3304870668849/20000000000000 : ℝ)^27
        have hw : |(1246834709/5000000000 : ℝ)|=(1246834709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1513257287/2000000000 : ℝ)|^35 ≤ (69662040918799/100000000000000 : ℝ)^27
        have hw : |(-1513257287/2000000000 : ℝ)|=(1513257287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309058_s1_s1_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2245069961/10000000000 : ℝ)*x 0 + (-644466677/2500000000 : ℝ)*x 1 + (-745422929/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2245069961/10000000000 : ℝ)^35 ≤ (7210604900999/50000000000000 : ℝ)^27 := by
    have hnat : (2245069961 : ℕ)^35*50000000000000^27 ≤ 7210604900999^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245069961 10000000000 7210604900999 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (644466677/2500000000 : ℝ)^35 ≤ (8625596064539/50000000000000 : ℝ)^27 := by
    have hnat : (644466677 : ℕ)^35*50000000000000^27 ≤ 8625596064539^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644466677 2500000000 8625596064539 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (745422929/1000000000 : ℝ)^35 ≤ (6832759804839/10000000000000 : ℝ)^27 := by
    have hnat : (745422929 : ℕ)^35*10000000000000^27 ≤ 6832759804839^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745422929 1000000000 6832759804839 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2245069961/10000000000 : ℝ), (-644466677/2500000000 : ℝ), (-745422929/1000000000 : ℝ)] ![(7210604900999/50000000000000 : ℝ), (8625596064539/50000000000000 : ℝ), (6832759804839/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2245069961/10000000000 : ℝ)|^35 ≤ (7210604900999/50000000000000 : ℝ)^27
        have hw : |(2245069961/10000000000 : ℝ)|=(2245069961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-644466677/2500000000 : ℝ)|^35 ≤ (8625596064539/50000000000000 : ℝ)^27
        have hw : |(-644466677/2500000000 : ℝ)|=(644466677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-745422929/1000000000 : ℝ)|^35 ≤ (6832759804839/10000000000000 : ℝ)^27
        have hw : |(-745422929/1000000000 : ℝ)|=(745422929/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309058_s1_s1_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6965067389/10000000000 : ℝ)*x 0 + (4248916957/10000000000 : ℝ)*x 1 + (907290601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6965067389/10000000000 : ℝ)^35 ≤ (2502906746351/4000000000000 : ℝ)^27 := by
    have hnat : (6965067389 : ℕ)^35*4000000000000^27 ≤ 2502906746351^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6965067389 10000000000 2502906746351 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4248916957/10000000000 : ℝ)^35 ≤ (32971481624627/100000000000000 : ℝ)^27 := by
    have hnat : (4248916957 : ℕ)^35*100000000000000^27 ≤ 32971481624627^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248916957 10000000000 32971481624627 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (907290601/10000000000 : ℝ)^35 ≤ (1113962426657/25000000000000 : ℝ)^27 := by
    have hnat : (907290601 : ℕ)^35*25000000000000^27 ≤ 1113962426657^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907290601 10000000000 1113962426657 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6965067389/10000000000 : ℝ), (4248916957/10000000000 : ℝ), (907290601/10000000000 : ℝ)] ![(2502906746351/4000000000000 : ℝ), (32971481624627/100000000000000 : ℝ), (1113962426657/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6965067389/10000000000 : ℝ)|^35 ≤ (2502906746351/4000000000000 : ℝ)^27
        have hw : |(6965067389/10000000000 : ℝ)|=(6965067389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4248916957/10000000000 : ℝ)|^35 ≤ (32971481624627/100000000000000 : ℝ)^27
        have hw : |(4248916957/10000000000 : ℝ)|=(4248916957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(907290601/10000000000 : ℝ)|^35 ≤ (1113962426657/25000000000000 : ℝ)^27
        have hw : |(907290601/10000000000 : ℝ)|=(907290601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309058_s1_s1_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1099755743/2500000000 : ℝ)*x 0 + (114997581/400000000 : ℝ)*x 1 + (-5460175569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099755743/2500000000 : ℝ)^35 ≤ (34489269962983/100000000000000 : ℝ)^27 := by
    have hnat : (1099755743 : ℕ)^35*100000000000000^27 ≤ 34489269962983^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099755743 2500000000 34489269962983 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114997581/400000000 : ℝ)^35 ≤ (1987112277007/10000000000000 : ℝ)^27 := by
    have hnat : (114997581 : ℕ)^35*10000000000000^27 ≤ 1987112277007^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114997581 400000000 1987112277007 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460175569/10000000000 : ℝ)^35 ≤ (22819803628621/50000000000000 : ℝ)^27 := by
    have hnat : (5460175569 : ℕ)^35*50000000000000^27 ≤ 22819803628621^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460175569 10000000000 22819803628621 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1099755743/2500000000 : ℝ), (114997581/400000000 : ℝ), (-5460175569/10000000000 : ℝ)] ![(34489269962983/100000000000000 : ℝ), (1987112277007/10000000000000 : ℝ), (22819803628621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1099755743/2500000000 : ℝ)|^35 ≤ (34489269962983/100000000000000 : ℝ)^27
        have hw : |(-1099755743/2500000000 : ℝ)|=(1099755743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(114997581/400000000 : ℝ)|^35 ≤ (1987112277007/10000000000000 : ℝ)^27
        have hw : |(114997581/400000000 : ℝ)|=(114997581/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5460175569/10000000000 : ℝ)|^35 ≤ (22819803628621/50000000000000 : ℝ)^27
        have hw : |(-5460175569/10000000000 : ℝ)|=(5460175569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309058_s1_s1_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2717881367/10000000000 : ℝ)*x 0 + (-155126179/500000000 : ℝ)*x 1 + (-1676899463/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2717881367/10000000000 : ℝ)^35 ≤ (18475452662677/100000000000000 : ℝ)^27 := by
    have hnat : (2717881367 : ℕ)^35*100000000000000^27 ≤ 18475452662677^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717881367 10000000000 18475452662677 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155126179/500000000 : ℝ)^35 ≤ (10966856460543/50000000000000 : ℝ)^27 := by
    have hnat : (155126179 : ℕ)^35*50000000000000^27 ≤ 10966856460543^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155126179 500000000 10966856460543 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1676899463/2500000000 : ℝ)^35 ≤ (59590834390301/100000000000000 : ℝ)^27 := by
    have hnat : (1676899463 : ℕ)^35*100000000000000^27 ≤ 59590834390301^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676899463 2500000000 59590834390301 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2717881367/10000000000 : ℝ), (-155126179/500000000 : ℝ), (-1676899463/2500000000 : ℝ)] ![(18475452662677/100000000000000 : ℝ), (10966856460543/50000000000000 : ℝ), (59590834390301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2717881367/10000000000 : ℝ)|^35 ≤ (18475452662677/100000000000000 : ℝ)^27
        have hw : |(2717881367/10000000000 : ℝ)|=(2717881367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-155126179/500000000 : ℝ)|^35 ≤ (10966856460543/50000000000000 : ℝ)^27
        have hw : |(-155126179/500000000 : ℝ)|=(155126179/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1676899463/2500000000 : ℝ)|^35 ≤ (59590834390301/100000000000000 : ℝ)^27
        have hw : |(-1676899463/2500000000 : ℝ)|=(1676899463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309058_s1_s1_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1475529231/2000000000 : ℝ)*x 0 + (3435773309/10000000000 : ℝ)*x 1 + (1362170357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1475529231/2000000000 : ℝ)^35 ≤ (33709504281099/50000000000000 : ℝ)^27 := by
    have hnat : (1475529231 : ℕ)^35*50000000000000^27 ≤ 33709504281099^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1475529231 2000000000 33709504281099 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3435773309/10000000000 : ℝ)^35 ≤ (12517577360569/50000000000000 : ℝ)^27 := by
    have hnat : (3435773309 : ℕ)^35*50000000000000^27 ≤ 12517577360569^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3435773309 10000000000 12517577360569 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362170357/10000000000 : ℝ)^35 ≤ (1886459177391/25000000000000 : ℝ)^27 := by
    have hnat : (1362170357 : ℕ)^35*25000000000000^27 ≤ 1886459177391^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362170357 10000000000 1886459177391 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1475529231/2000000000 : ℝ), (3435773309/10000000000 : ℝ), (1362170357/10000000000 : ℝ)] ![(33709504281099/50000000000000 : ℝ), (12517577360569/50000000000000 : ℝ), (1886459177391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1475529231/2000000000 : ℝ)|^35 ≤ (33709504281099/50000000000000 : ℝ)^27
        have hw : |(1475529231/2000000000 : ℝ)|=(1475529231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3435773309/10000000000 : ℝ)|^35 ≤ (12517577360569/50000000000000 : ℝ)^27
        have hw : |(3435773309/10000000000 : ℝ)|=(3435773309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1362170357/10000000000 : ℝ)|^35 ≤ (1886459177391/25000000000000 : ℝ)^27
        have hw : |(1362170357/10000000000 : ℝ)|=(1362170357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309058_s1_s1_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1010488821/5000000000 : ℝ)*x 0 + (4507268593/5000000000 : ℝ)*x 1 + (11/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1010488821/5000000000 : ℝ)^35 ≤ (12583514562771/100000000000000 : ℝ)^27 := by
    have hnat : (1010488821 : ℕ)^35*100000000000000^27 ≤ 12583514562771^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010488821 5000000000 12583514562771 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507268593/5000000000 : ℝ)^35 ≤ (43708242652849/50000000000000 : ℝ)^27 := by
    have hnat : (4507268593 : ℕ)^35*50000000000000^27 ≤ 43708242652849^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507268593 5000000000 43708242652849 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11/80000000 : ℝ)^35 ≤ (31853/25000000000000 : ℝ)^27 := by
    have hnat : (11 : ℕ)^35*25000000000000^27 ≤ 31853^27*80000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11 80000000 31853 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1010488821/5000000000 : ℝ), (4507268593/5000000000 : ℝ), (11/80000000 : ℝ)] ![(12583514562771/100000000000000 : ℝ), (43708242652849/50000000000000 : ℝ), (31853/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1010488821/5000000000 : ℝ)|^35 ≤ (12583514562771/100000000000000 : ℝ)^27
        have hw : |(1010488821/5000000000 : ℝ)|=(1010488821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507268593/5000000000 : ℝ)|^35 ≤ (43708242652849/50000000000000 : ℝ)^27
        have hw : |(4507268593/5000000000 : ℝ)|=(4507268593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11/80000000 : ℝ)|^35 ≤ (31853/25000000000000 : ℝ)^27
        have hw : |(11/80000000 : ℝ)|=(11/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309058_s1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((92119/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(92119/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8509/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8509/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1589/2000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1589/2000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((77227/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(77227/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70009/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70009/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-53459/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-53459/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (91323/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (92119/100000 : ℝ) ^ (69/16 : ℝ) ≤ (14037377670120773197/20000000000000000000 : ℝ) := by
    have hpowers : (92119/100000 : ℝ)^69 ≤ (14037377670120773197/20000000000000000000 : ℝ)^16 := by
      have hnat : (92119 : ℕ)^69*20000000000000000000^16 ≤ 14037377670120773197^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92119 100000 14037377670120773197 20000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92119/100000 : ℝ)) (X := (14037377670120773197/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (34037377670120773197/20000000000000000000 : ℝ) ≤ (11312226198390671/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (34037377670120773197/20000000000000000000 : ℝ)^16 ≤ (11312226198390671/10000000000000000 : ℝ)^69 := by
      have hnat : (34037377670120773197 : ℕ)^16*10000000000000000^69 ≤ 11312226198390671^69*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34037377670120773197 20000000000000000000 11312226198390671 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11312226198390671/10000000000000000 : ℝ)) (X := (34037377670120773197/20000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (24037377670120773197/10000000000000000000 : ℝ) ≤ (382976093665283/312500000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (24037377670120773197/10000000000000000000 : ℝ)^16 ≤ (382976093665283/312500000000000 : ℝ)^69 := by
      have hnat : (24037377670120773197 : ℕ)^16*312500000000000^69 ≤ 382976093665283^69*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24037377670120773197 10000000000000000000 382976093665283 312500000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (382976093665283/312500000000000 : ℝ)) (X := (24037377670120773197/10000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1312226198390671/9211900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(188601759779677/1842380000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (92119/100000 : ℝ)) (alpha := (1312226198390671/9211900000000000 : ℝ)) (beta := (188601759779677/1842380000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (92119/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1312226198390671/9211900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(188601759779677/1842380000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (8509/10000 : ℝ) ^ (69/16 : ℝ) ≤ (49842651002178266641/100000000000000000000 : ℝ) := by
    have hpowers : (8509/10000 : ℝ)^69 ≤ (49842651002178266641/100000000000000000000 : ℝ)^16 := by
      have hnat : (8509 : ℕ)^69*100000000000000000000^16 ≤ 49842651002178266641^16*10000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8509 10000 49842651002178266641 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8509/10000 : ℝ)) (X := (49842651002178266641/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (149842651002178266641/100000000000000000000 : ℝ) ≤ (10983153678766057/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (149842651002178266641/100000000000000000000 : ℝ)^16 ≤ (10983153678766057/10000000000000000 : ℝ)^69 := by
      have hnat : (149842651002178266641 : ℕ)^16*10000000000000000^69 ≤ 10983153678766057^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        149842651002178266641 100000000000000000000 10983153678766057 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10983153678766057/10000000000000000 : ℝ)) (X := (149842651002178266641/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (99842651002178266641/50000000000000000000 : ℝ) ≤ (2934847105137683/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (99842651002178266641/50000000000000000000 : ℝ)^16 ≤ (2934847105137683/2500000000000000 : ℝ)^69 := by
      have hnat : (99842651002178266641 : ℕ)^16*2500000000000000^69 ≤ 2934847105137683^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        99842651002178266641 50000000000000000000 2934847105137683 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2934847105137683/2500000000000000 : ℝ)) (X := (99842651002178266641/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(14673935503971/127000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(30249389671387/340360000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (8509/10000 : ℝ)) (alpha := (14673935503971/127000000000000 : ℝ)) (beta := (30249389671387/340360000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (8509/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(14673935503971/127000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(30249389671387/340360000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1589/2000 : ℝ) ^ (69/16 : ℝ) ≤ (2317581245337449709/6250000000000000000 : ℝ) := by
    have hpowers : (1589/2000 : ℝ)^69 ≤ (2317581245337449709/6250000000000000000 : ℝ)^16 := by
      have hnat : (1589 : ℕ)^69*6250000000000000000^16 ≤ 2317581245337449709^16*2000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1589 2000 2317581245337449709 6250000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1589/2000 : ℝ)) (X := (2317581245337449709/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (8567581245337449709/6250000000000000000 : ℝ) ≤ (10758780920994593/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (8567581245337449709/6250000000000000000 : ℝ)^16 ≤ (10758780920994593/10000000000000000 : ℝ)^69 := by
      have hnat : (8567581245337449709 : ℕ)^16*10000000000000000^69 ≤ 10758780920994593^69*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8567581245337449709 6250000000000000000 10758780920994593 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10758780920994593/10000000000000000 : ℝ)) (X := (8567581245337449709/6250000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (5442581245337449709/3125000000000000000 : ℝ) ≤ (1137296230729813/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (5442581245337449709/3125000000000000000 : ℝ)^16 ≤ (1137296230729813/1000000000000000 : ℝ)^69 := by
      have hnat : (5442581245337449709 : ℕ)^16*1000000000000000^69 ≤ 1137296230729813^69*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5442581245337449709 3125000000000000000 1137296230729813 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1137296230729813/1000000000000000 : ℝ)) (X := (5442581245337449709/3125000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(108397274427799/1135000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(614181386303537/7945000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1589/2000 : ℝ)) (alpha := (108397274427799/1135000000000000 : ℝ)) (beta := (614181386303537/7945000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1589/2000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(108397274427799/1135000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(614181386303537/7945000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1561787807/5000000000 : ℝ)*X 0 0+(3043499217/10000000000 : ℝ)*X 0 1+(-6435726743/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309058_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((15996387/50000000 : ℝ)*X 1 0+(-3087012241/10000000000 : ℝ)*X 1 1+(-3169629761/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309058_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2213498189/10000000000 : ℝ)*X 0 0+(422122813/2500000000 : ℝ)*X 0 1+(-8081580559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309058_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((74225889/312500000 : ℝ)*X 1 0+(-1701296819/10000000000 : ℝ)*X 1 1+(-7961891019/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309058_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((84944191/200000000 : ℝ)*X 2 0+(1296598019/2000000000 : ℝ)*X 2 1+(1696399453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309058_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((2617891919/10000000000 : ℝ)*X 0 0+(8612852081/10000000000 : ℝ)*X 0 1+(-84261/10000000000 : ℝ)*X 0 2+(2617891919/10000000000 : ℝ)*X 1 0+(8612852081/10000000000 : ℝ)*X 1 1+(-84261/10000000000 : ℝ)*X 1 2+(2617891919/10000000000 : ℝ)*X 2 0+(8612852081/10000000000 : ℝ)*X 2 1+(-84261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309058_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-43434847/200000000 : ℝ)*X 0 0+(1246834709/5000000000 : ℝ)*X 0 1+(-1513257287/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309058_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2245069961/10000000000 : ℝ)*X 1 0+(-644466677/2500000000 : ℝ)*X 1 1+(-745422929/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309058_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6965067389/10000000000 : ℝ)*X 2 0+(4248916957/10000000000 : ℝ)*X 2 1+(907290601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309058_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-1099755743/2500000000 : ℝ)*X 0 0+(114997581/400000000 : ℝ)*X 0 1+(-5460175569/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309058_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((2717881367/10000000000 : ℝ)*X 1 0+(-155126179/500000000 : ℝ)*X 1 1+(-1676899463/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309058_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1475529231/2000000000 : ℝ)*X 2 0+(3435773309/10000000000 : ℝ)*X 2 1+(1362170357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309058_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1010488821/5000000000 : ℝ)*X 0 0+(4507268593/5000000000 : ℝ)*X 0 1+(11/80000000 : ℝ)*X 0 2+(1010488821/5000000000 : ℝ)*X 1 0+(4507268593/5000000000 : ℝ)*X 1 1+(11/80000000 : ℝ)*X 1 2+(1010488821/5000000000 : ℝ)*X 2 0+(4507268593/5000000000 : ℝ)*X 2 1+(11/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309058_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((77227/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(77227/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (878625463674163225518927/125414491360000000000000000000 : ℝ) := by norm_num
    linear_combination (422640037817/500000000000 : ℝ)*(base7) + (1673/15625000000 : ℝ)*(base49) + (244811/62500000000 : ℝ)*(base53) + (68511/40000000000 : ℝ)*(base60) + (2103558369309/1000000000000 : ℝ)*(major_s1_0) + (2103558369309/1000000000000 : ℝ)*(major_s1_1) + (2103554452333/1000000000000 : ℝ)*(major_s1_2) + (237152031013/100000000000 : ℝ)*(sp_s1_7) + (474303694717/200000000000 : ℝ)*(sp_s1_8) + (7411094781/3125000000 : ℝ)*(sp_s1_9) + (2166205579461/1000000000000 : ℝ)*(sp_s1_13) + (13051407/500000000000 : ℝ)*(sp_s1_14) + (27939359/1000000000000 : ℝ)*(sp_s1_15) + (7576981/500000000000 : ℝ)*(sp_s1_27) + (1320940657789/1000000000000 : ℝ)*(f.failure) + (7411094781/3125000000 : ℝ)*(f.sum) + (56442442387219/140766601562500000000000000 : ℝ)*base63 + (834169538630679/7945000000000000000000000000 : ℝ)*base64 + (237576527543499/340360000000000000000000000 : ℝ)*base67 + (292025793422067/1135000000000000000000000000 : ℝ)*base68 + (375323529389239219249/731885455000000000000000000000000 : ℝ)*base71 + (856877694660641/1842380000000000000000000000 : ℝ)*base73 + (72219007614061/127000000000000000000000000 : ℝ)*base74 + (4371497648034531/9211900000000000000000000000 : ℝ)*base76 + (117279352276586367/1254144913600000000000000000000 : ℝ)*base79 + (24883/100000000000000000 : ℝ)*base87 + (24883/100000000000000000 : ℝ)*base89 + (24883/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70009/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70009/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2408946738026451726801638649/182971363750000000000000000000000 : ℝ) := by norm_num
    linear_combination (2562930005777/1000000000000 : ℝ)*(base5) + (781936792547/1000000000000 : ℝ)*(base7) + (294874775207/1000000000000 : ℝ)*(base59) + (1798548334287/1000000000000 : ℝ)*(base60) + (11078821337/3906250000 : ℝ)*(major_s1_0) + (11078821337/3906250000 : ℝ)*(major_s1_1) + (11078821337/3906250000 : ℝ)*(major_s1_2) + (29601/25000000000 : ℝ)*(sp_s1_0) + (34289019/1000000000000 : ℝ)*(sp_s1_1) + (14148707/200000000000 : ℝ)*(sp_s1_8) + (683059796133/200000000000 : ℝ)*(sp_s1_14) + (3415195132151/1000000000000 : ℝ)*(sp_s1_15) + (239128588839/40000000000 : ℝ)*(sp_s1_16) + (15449507/1000000000000 : ℝ)*(sp_s1_23) + (178099321323/100000000000 : ℝ)*(f.failure) + (683060032941/200000000000 : ℝ)*(f.sum) + (609428867797183/18018125000000000000000000000 : ℝ)*base63 + (530939710583617/993125000000000000000000000 : ℝ)*base64 + (21438249509271/85090000000000000000000000 : ℝ)*base67 + (36492997269457/283750000000000000000000000 : ℝ)*base68 + (16456155818219624749/45742840937500000000000000000000 : ℝ)*base70 + (213198847999959/921190000000000000000000000 : ℝ)*base73 + (2788988046243/7937500000000000000000000 : ℝ)*base74 + (830335803040927/2302975000000000000000000000 : ℝ)*base76 + (182603636277119201/3919202855000000000000000000000 : ℝ)*base78 + (3781/10000000000000000 : ℝ)*base87 + (3781/10000000000000000 : ℝ)*base89 + (3781/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-53459/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-53459/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7171578963748584472474795347/1452335199765625000000000000000000 : ℝ) := by norm_num
    linear_combination (62031303443/1000000000000 : ℝ)*(base5) + (382815032133/1000000000000 : ℝ)*(base7) + (34880023031/200000000000 : ℝ)*(base33) + (87955868289/200000000000 : ℝ)*(base44) + (2355007/1000000000000 : ℝ)*(base60) + (1049608036727/500000000000 : ℝ)*(major_s1_0) + (458459211791/250000000000 : ℝ)*(major_s1_1) + (2273616188609/1000000000000 : ℝ)*(major_s1_2) + (151491259/1000000000000 : ℝ)*(sp_s1_1) + (1340779/40000000000 : ℝ)*(sp_s1_13) + (360804489267/125000000000 : ℝ)*(sp_s1_21) + (2272104966277/1000000000000 : ℝ)*(sp_s1_22) + (110962684097/40000000000 : ℝ)*(sp_s1_23) + (654350118497/500000000000 : ℝ)*(sp_s1_27) + (57109174769/40000000000 : ℝ)*(f.failure) + (360804489267/125000000000 : ℝ)*(f.sum) + (43674375910399617/144145000000000000000000000000 : ℝ)*base62 + (2864445851715467/7945000000000000000000000000 : ℝ)*base64 + (13287465218549/42545000000000000000000000 : ℝ)*base67 + (623820572023591/1135000000000000000000000000 : ℝ)*base68 + (66438895636015288773/731885455000000000000000000000000 : ℝ)*base70 + (8976019258781/28787187500000000000000000 : ℝ)*base73 + (21445383017839/31750000000000000000000000 : ℝ)*base74 + (1403747249823163/4605950000000000000000000000 : ℝ)*base76 + (531959082614592233/3919202855000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (2943/4000000000000000 : ℝ)*base87 + (2943/4000000000000000 : ℝ)*base89 + (2943/4000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((92119/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(92119/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8509/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8509/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1589/2000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1589/2000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((77227/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(77227/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70009/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70009/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-53459/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-53459/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309058_s1 p hpa hpb X hX hprev0

#print axioms solution

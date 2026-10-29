-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c318083_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:25:07.53959+00:00
-- url     : https://prove2.me/submissions/c11296f5-b846-4b9f-a379-9ae6519f50f0

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
theorem collision_support_c318083_s1_s1_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-28404967/125000000 : ℝ)*x 0 + (18710913/39062500 : ℝ)*x 1 + (5258921377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28404967/125000000 : ℝ)^79 ≤ (15597382090833/100000000000000 : ℝ)^63 := by
    have hnat : (28404967 : ℕ)^79*100000000000000^63 ≤ 15597382090833^63*125000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28404967 125000000 15597382090833 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18710913/39062500 : ℝ)^79 ≤ (2483305704441/6250000000000 : ℝ)^63 := by
    have hnat : (18710913 : ℕ)^79*6250000000000^63 ≤ 2483305704441^63*39062500^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18710913 39062500 2483305704441 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258921377/10000000000 : ℝ)^79 ≤ (4466972662303/10000000000000 : ℝ)^63 := by
    have hnat : (5258921377 : ℕ)^79*10000000000000^63 ≤ 4466972662303^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258921377 10000000000 4466972662303 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-28404967/125000000 : ℝ), (18710913/39062500 : ℝ), (5258921377/10000000000 : ℝ)] ![(15597382090833/100000000000000 : ℝ), (2483305704441/6250000000000 : ℝ), (4466972662303/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-28404967/125000000 : ℝ)|^79 ≤ (15597382090833/100000000000000 : ℝ)^63
        have hw : |(-28404967/125000000 : ℝ)|=(28404967/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(18710913/39062500 : ℝ)|^79 ≤ (2483305704441/6250000000000 : ℝ)^63
        have hw : |(18710913/39062500 : ℝ)|=(18710913/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258921377/10000000000 : ℝ)|^79 ≤ (4466972662303/10000000000000 : ℝ)^63
        have hw : |(5258921377/10000000000 : ℝ)|=(5258921377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318083_s1_s1_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3375849333/5000000000 : ℝ)*x 0 + (-824726799/10000000000 : ℝ)*x 1 + (4281512297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3375849333/5000000000 : ℝ)^79 ≤ (61106777500439/100000000000000 : ℝ)^63 := by
    have hnat : (3375849333 : ℕ)^79*100000000000000^63 ≤ 61106777500439^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3375849333 5000000000 61106777500439 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (824726799/10000000000 : ℝ)^79 ≤ (4376100395689/100000000000000 : ℝ)^63 := by
    have hnat : (824726799 : ℕ)^79*100000000000000^63 ≤ 4376100395689^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824726799 10000000000 4376100395689 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4281512297/10000000000 : ℝ)^79 ≤ (6903424418873/20000000000000 : ℝ)^63 := by
    have hnat : (4281512297 : ℕ)^79*20000000000000^63 ≤ 6903424418873^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4281512297 10000000000 6903424418873 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3375849333/5000000000 : ℝ), (-824726799/10000000000 : ℝ), (4281512297/10000000000 : ℝ)] ![(61106777500439/100000000000000 : ℝ), (4376100395689/100000000000000 : ℝ), (6903424418873/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3375849333/5000000000 : ℝ)|^79 ≤ (61106777500439/100000000000000 : ℝ)^63
        have hw : |(3375849333/5000000000 : ℝ)|=(3375849333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-824726799/10000000000 : ℝ)|^79 ≤ (4376100395689/100000000000000 : ℝ)^63
        have hw : |(-824726799/10000000000 : ℝ)|=(824726799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4281512297/10000000000 : ℝ)|^79 ≤ (6903424418873/20000000000000 : ℝ)^63
        have hw : |(4281512297/10000000000 : ℝ)|=(4281512297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318083_s1_s1_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (887868841/2500000000 : ℝ)*x 0 + (6366179551/10000000000 : ℝ)*x 1 + (-115561309/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (887868841/2500000000 : ℝ)^79 ≤ (27304040279303/100000000000000 : ℝ)^63 := by
    have hnat : (887868841 : ℕ)^79*100000000000000^63 ≤ 27304040279303^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887868841 2500000000 27304040279303 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6366179551/10000000000 : ℝ)^79 ≤ (56763654195473/100000000000000 : ℝ)^63 := by
    have hnat : (6366179551 : ℕ)^79*100000000000000^63 ≤ 56763654195473^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6366179551 10000000000 56763654195473 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115561309/500000000 : ℝ)^79 ≤ (3983076377123/25000000000000 : ℝ)^63 := by
    have hnat : (115561309 : ℕ)^79*25000000000000^63 ≤ 3983076377123^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115561309 500000000 3983076377123 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(887868841/2500000000 : ℝ), (6366179551/10000000000 : ℝ), (-115561309/500000000 : ℝ)] ![(27304040279303/100000000000000 : ℝ), (56763654195473/100000000000000 : ℝ), (3983076377123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(887868841/2500000000 : ℝ)|^79 ≤ (27304040279303/100000000000000 : ℝ)^63
        have hw : |(887868841/2500000000 : ℝ)|=(887868841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6366179551/10000000000 : ℝ)|^79 ≤ (56763654195473/100000000000000 : ℝ)^63
        have hw : |(6366179551/10000000000 : ℝ)|=(6366179551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-115561309/500000000 : ℝ)|^79 ≤ (3983076377123/25000000000000 : ℝ)^63
        have hw : |(-115561309/500000000 : ℝ)|=(115561309/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318083_s1_s1_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2313022507/10000000000 : ℝ)*x 0 + (950250567/2000000000 : ℝ)*x 1 + (1052762469/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2313022507/10000000000 : ℝ)^79 ≤ (15947834775917/100000000000000 : ℝ)^63 := by
    have hnat : (2313022507 : ℕ)^79*100000000000000^63 ≤ 15947834775917^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313022507 10000000000 15947834775917 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (950250567/2000000000 : ℝ)^79 ≤ (39330337195177/100000000000000 : ℝ)^63 := by
    have hnat : (950250567 : ℕ)^79*100000000000000^63 ≤ 39330337195177^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950250567 2000000000 39330337195177 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052762469/2000000000 : ℝ)^79 ≤ (44721828006429/100000000000000 : ℝ)^63 := by
    have hnat : (1052762469 : ℕ)^79*100000000000000^63 ≤ 44721828006429^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052762469 2000000000 44721828006429 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2313022507/10000000000 : ℝ), (950250567/2000000000 : ℝ), (1052762469/2000000000 : ℝ)] ![(15947834775917/100000000000000 : ℝ), (39330337195177/100000000000000 : ℝ), (44721828006429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2313022507/10000000000 : ℝ)|^79 ≤ (15947834775917/100000000000000 : ℝ)^63
        have hw : |(-2313022507/10000000000 : ℝ)|=(2313022507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(950250567/2000000000 : ℝ)|^79 ≤ (39330337195177/100000000000000 : ℝ)^63
        have hw : |(950250567/2000000000 : ℝ)|=(950250567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052762469/2000000000 : ℝ)|^79 ≤ (44721828006429/100000000000000 : ℝ)^63
        have hw : |(1052762469/2000000000 : ℝ)|=(1052762469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318083_s1_s1_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3251284183/5000000000 : ℝ)*x 0 + (-14620891/2000000000 : ℝ)*x 1 + (1239726017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3251284183/5000000000 : ℝ)^79 ≤ (58292734999537/100000000000000 : ℝ)^63 := by
    have hnat : (3251284183 : ℕ)^79*100000000000000^63 ≤ 58292734999537^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3251284183 5000000000 58292734999537 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14620891/2000000000 : ℝ)^79 ≤ (104814989633/50000000000000 : ℝ)^63 := by
    have hnat : (14620891 : ℕ)^79*50000000000000^63 ≤ 104814989633^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14620891 2000000000 104814989633 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1239726017/2500000000 : ℝ)^79 ≤ (20748817506271/50000000000000 : ℝ)^63 := by
    have hnat : (1239726017 : ℕ)^79*50000000000000^63 ≤ 20748817506271^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239726017 2500000000 20748817506271 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3251284183/5000000000 : ℝ), (-14620891/2000000000 : ℝ), (1239726017/2500000000 : ℝ)] ![(58292734999537/100000000000000 : ℝ), (104814989633/50000000000000 : ℝ), (20748817506271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3251284183/5000000000 : ℝ)|^79 ≤ (58292734999537/100000000000000 : ℝ)^63
        have hw : |(3251284183/5000000000 : ℝ)|=(3251284183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-14620891/2000000000 : ℝ)|^79 ≤ (104814989633/50000000000000 : ℝ)^63
        have hw : |(-14620891/2000000000 : ℝ)|=(14620891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1239726017/2500000000 : ℝ)|^79 ≤ (20748817506271/50000000000000 : ℝ)^63
        have hw : |(1239726017/2500000000 : ℝ)|=(1239726017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318083_s1_s1_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (624411959/2000000000 : ℝ)*x 0 + (7191008237/10000000000 : ℝ)*x 1 + (-418660793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (624411959/2000000000 : ℝ)^79 ≤ (23229792746721/100000000000000 : ℝ)^63 := by
    have hnat : (624411959 : ℕ)^79*100000000000000^63 ≤ 23229792746721^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624411959 2000000000 23229792746721 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7191008237/10000000000 : ℝ)^79 ≤ (6613310875119/10000000000000 : ℝ)^63 := by
    have hnat : (7191008237 : ℕ)^79*10000000000000^63 ≤ 6613310875119^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7191008237 10000000000 6613310875119 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418660793/2500000000 : ℝ)^79 ≤ (10637098487437/100000000000000 : ℝ)^63 := by
    have hnat : (418660793 : ℕ)^79*100000000000000^63 ≤ 10637098487437^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418660793 2500000000 10637098487437 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(624411959/2000000000 : ℝ), (7191008237/10000000000 : ℝ), (-418660793/2500000000 : ℝ)] ![(23229792746721/100000000000000 : ℝ), (6613310875119/10000000000000 : ℝ), (10637098487437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(624411959/2000000000 : ℝ)|^79 ≤ (23229792746721/100000000000000 : ℝ)^63
        have hw : |(624411959/2000000000 : ℝ)|=(624411959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7191008237/10000000000 : ℝ)|^79 ≤ (6613310875119/10000000000000 : ℝ)^63
        have hw : |(7191008237/10000000000 : ℝ)|=(7191008237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418660793/2500000000 : ℝ)|^79 ≤ (10637098487437/100000000000000 : ℝ)^63
        have hw : |(-418660793/2500000000 : ℝ)|=(418660793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318083_s1_s1_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (11068101/40000000 : ℝ)*x 0 + (72817101/156250000 : ℝ)*x 1 + (4972943587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11068101/40000000 : ℝ)^79 ≤ (19966510420687/100000000000000 : ℝ)^63 := by
    have hnat : (11068101 : ℕ)^79*100000000000000^63 ≤ 19966510420687^63*40000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11068101 40000000 19966510420687 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (72817101/156250000 : ℝ)^79 ≤ (9597119159613/25000000000000 : ℝ)^63 := by
    have hnat : (72817101 : ℕ)^79*25000000000000^63 ≤ 9597119159613^63*156250000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72817101 156250000 9597119159613 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4972943587/10000000000 : ℝ)^79 ≤ (41645012927419/100000000000000 : ℝ)^63 := by
    have hnat : (4972943587 : ℕ)^79*100000000000000^63 ≤ 41645012927419^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4972943587 10000000000 41645012927419 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(11068101/40000000 : ℝ), (72817101/156250000 : ℝ), (4972943587/10000000000 : ℝ)] ![(19966510420687/100000000000000 : ℝ), (9597119159613/25000000000000 : ℝ), (41645012927419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(11068101/40000000 : ℝ)|^79 ≤ (19966510420687/100000000000000 : ℝ)^63
        have hw : |(11068101/40000000 : ℝ)|=(11068101/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(72817101/156250000 : ℝ)|^79 ≤ (9597119159613/25000000000000 : ℝ)^63
        have hw : |(72817101/156250000 : ℝ)|=(72817101/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4972943587/10000000000 : ℝ)|^79 ≤ (41645012927419/100000000000000 : ℝ)^63
        have hw : |(4972943587/10000000000 : ℝ)|=(4972943587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318083_s1_s1_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-187344859/1250000000 : ℝ)*x 0 + (1936383241/5000000000 : ℝ)*x 1 + (83515653/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (187344859/1250000000 : ℝ)^79 ≤ (578460648793/6250000000000 : ℝ)^63 := by
    have hnat : (187344859 : ℕ)^79*6250000000000^63 ≤ 578460648793^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187344859 1250000000 578460648793 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1936383241/5000000000 : ℝ)^79 ≤ (1902268515411/6250000000000 : ℝ)^63 := by
    have hnat : (1936383241 : ℕ)^79*6250000000000^63 ≤ 1902268515411^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936383241 5000000000 1902268515411 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83515653/125000000 : ℝ)^79 ≤ (30154166677669/50000000000000 : ℝ)^63 := by
    have hnat : (83515653 : ℕ)^79*50000000000000^63 ≤ 30154166677669^63*125000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83515653 125000000 30154166677669 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-187344859/1250000000 : ℝ), (1936383241/5000000000 : ℝ), (83515653/125000000 : ℝ)] ![(578460648793/6250000000000 : ℝ), (1902268515411/6250000000000 : ℝ), (30154166677669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-187344859/1250000000 : ℝ)|^79 ≤ (578460648793/6250000000000 : ℝ)^63
        have hw : |(-187344859/1250000000 : ℝ)|=(187344859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1936383241/5000000000 : ℝ)|^79 ≤ (1902268515411/6250000000000 : ℝ)^63
        have hw : |(1936383241/5000000000 : ℝ)|=(1936383241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(83515653/125000000 : ℝ)|^79 ≤ (30154166677669/50000000000000 : ℝ)^63
        have hw : |(83515653/125000000 : ℝ)|=(83515653/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318083_s1_s1_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7699928293/10000000000 : ℝ)*x 0 + (-32885089/500000000 : ℝ)*x 1 + (1636736481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7699928293/10000000000 : ℝ)^79 ≤ (72053967820343/100000000000000 : ℝ)^63 := by
    have hnat : (7699928293 : ℕ)^79*100000000000000^63 ≤ 72053967820343^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7699928293 10000000000 72053967820343 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32885089/500000000 : ℝ)^79 ≤ (823731965037/25000000000000 : ℝ)^63 := by
    have hnat : (32885089 : ℕ)^79*25000000000000^63 ≤ 823731965037^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32885089 500000000 823731965037 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1636736481/5000000000 : ℝ)^79 ≤ (24651104300541/100000000000000 : ℝ)^63 := by
    have hnat : (1636736481 : ℕ)^79*100000000000000^63 ≤ 24651104300541^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1636736481 5000000000 24651104300541 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7699928293/10000000000 : ℝ), (-32885089/500000000 : ℝ), (1636736481/5000000000 : ℝ)] ![(72053967820343/100000000000000 : ℝ), (823731965037/25000000000000 : ℝ), (24651104300541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7699928293/10000000000 : ℝ)|^79 ≤ (72053967820343/100000000000000 : ℝ)^63
        have hw : |(7699928293/10000000000 : ℝ)|=(7699928293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32885089/500000000 : ℝ)|^79 ≤ (823731965037/25000000000000 : ℝ)^63
        have hw : |(-32885089/500000000 : ℝ)|=(32885089/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1636736481/5000000000 : ℝ)|^79 ≤ (24651104300541/100000000000000 : ℝ)^63
        have hw : |(1636736481/5000000000 : ℝ)|=(1636736481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318083_s1_s1_16 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (363178453/1000000000 : ℝ)*x 0 + (3416361029/5000000000 : ℝ)*x 1 + (-790194203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (363178453/1000000000 : ℝ)^79 ≤ (1755030042329/6250000000000 : ℝ)^63 := by
    have hnat : (363178453 : ℕ)^79*6250000000000^63 ≤ 1755030042329^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363178453 1000000000 1755030042329 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3416361029/5000000000 : ℝ)^79 ≤ (62027720252283/100000000000000 : ℝ)^63 := by
    have hnat : (3416361029 : ℕ)^79*100000000000000^63 ≤ 62027720252283^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3416361029 5000000000 62027720252283 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (790194203/5000000000 : ℝ)^79 ≤ (395671961947/4000000000000 : ℝ)^63 := by
    have hnat : (790194203 : ℕ)^79*4000000000000^63 ≤ 395671961947^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790194203 5000000000 395671961947 4000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(363178453/1000000000 : ℝ), (3416361029/5000000000 : ℝ), (-790194203/5000000000 : ℝ)] ![(1755030042329/6250000000000 : ℝ), (62027720252283/100000000000000 : ℝ), (395671961947/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(363178453/1000000000 : ℝ)|^79 ≤ (1755030042329/6250000000000 : ℝ)^63
        have hw : |(363178453/1000000000 : ℝ)|=(363178453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3416361029/5000000000 : ℝ)|^79 ≤ (62027720252283/100000000000000 : ℝ)^63
        have hw : |(3416361029/5000000000 : ℝ)|=(3416361029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-790194203/5000000000 : ℝ)|^79 ≤ (395671961947/4000000000000 : ℝ)^63
        have hw : |(-790194203/5000000000 : ℝ)|=(790194203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318083_s1_s1_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2500665521/10000000000 : ℝ)*x 0 + (387452999/1000000000 : ℝ)*x 1 + (5932716249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2500665521/10000000000 : ℝ)^79 ≤ (4396639406387/25000000000000 : ℝ)^63 := by
    have hnat : (2500665521 : ℕ)^79*25000000000000^63 ≤ 4396639406387^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2500665521 10000000000 4396639406387 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (387452999/1000000000 : ℝ)^79 ≤ (951677394967/3125000000000 : ℝ)^63 := by
    have hnat : (387452999 : ℕ)^79*3125000000000^63 ≤ 951677394967^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387452999 1000000000 951677394967 3125000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5932716249/10000000000 : ℝ)^79 ≤ (51959765723959/100000000000000 : ℝ)^63 := by
    have hnat : (5932716249 : ℕ)^79*100000000000000^63 ≤ 51959765723959^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5932716249 10000000000 51959765723959 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2500665521/10000000000 : ℝ), (387452999/1000000000 : ℝ), (5932716249/10000000000 : ℝ)] ![(4396639406387/25000000000000 : ℝ), (951677394967/3125000000000 : ℝ), (51959765723959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2500665521/10000000000 : ℝ)|^79 ≤ (4396639406387/25000000000000 : ℝ)^63
        have hw : |(2500665521/10000000000 : ℝ)|=(2500665521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(387452999/1000000000 : ℝ)|^79 ≤ (951677394967/3125000000000 : ℝ)^63
        have hw : |(387452999/1000000000 : ℝ)|=(387452999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5932716249/10000000000 : ℝ)|^79 ≤ (51959765723959/100000000000000 : ℝ)^63
        have hw : |(5932716249/10000000000 : ℝ)|=(5932716249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318083_s1_s1_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-854483467/5000000000 : ℝ)*x 0 + (2716680121/5000000000 : ℝ)*x 1 + (5059249541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854483467/5000000000 : ℝ)^79 ≤ (10911196249729/100000000000000 : ℝ)^63 := by
    have hnat : (854483467 : ℕ)^79*100000000000000^63 ≤ 10911196249729^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854483467 5000000000 10911196249729 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716680121/5000000000 : ℝ)^79 ≤ (46535492032457/100000000000000 : ℝ)^63 := by
    have hnat : (2716680121 : ℕ)^79*100000000000000^63 ≤ 46535492032457^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716680121 5000000000 46535492032457 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5059249541/10000000000 : ℝ)^79 ≤ (42553311710157/100000000000000 : ℝ)^63 := by
    have hnat : (5059249541 : ℕ)^79*100000000000000^63 ≤ 42553311710157^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5059249541 10000000000 42553311710157 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-854483467/5000000000 : ℝ), (2716680121/5000000000 : ℝ), (5059249541/10000000000 : ℝ)] ![(10911196249729/100000000000000 : ℝ), (46535492032457/100000000000000 : ℝ), (42553311710157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-854483467/5000000000 : ℝ)|^79 ≤ (10911196249729/100000000000000 : ℝ)^63
        have hw : |(-854483467/5000000000 : ℝ)|=(854483467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716680121/5000000000 : ℝ)|^79 ≤ (46535492032457/100000000000000 : ℝ)^63
        have hw : |(2716680121/5000000000 : ℝ)|=(2716680121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5059249541/10000000000 : ℝ)|^79 ≤ (42553311710157/100000000000000 : ℝ)^63
        have hw : |(5059249541/10000000000 : ℝ)|=(5059249541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318083_s1_s1_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (741747911/1000000000 : ℝ)*x 0 + (-73569883/10000000000 : ℝ)*x 1 + (491655671/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (741747911/1000000000 : ℝ)^79 ≤ (13751040294663/20000000000000 : ℝ)^63 := by
    have hnat : (741747911 : ℕ)^79*20000000000000^63 ≤ 13751040294663^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741747911 1000000000 13751040294663 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73569883/10000000000 : ℝ)^79 ≤ (211304918323/100000000000000 : ℝ)^63 := by
    have hnat : (73569883 : ℕ)^79*100000000000000^63 ≤ 211304918323^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73569883 10000000000 211304918323 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491655671/1250000000 : ℝ)^79 ≤ (24244916873/78125000000 : ℝ)^63 := by
    have hnat : (491655671 : ℕ)^79*78125000000^63 ≤ 24244916873^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491655671 1250000000 24244916873 78125000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(741747911/1000000000 : ℝ), (-73569883/10000000000 : ℝ), (491655671/1250000000 : ℝ)] ![(13751040294663/20000000000000 : ℝ), (211304918323/100000000000000 : ℝ), (24244916873/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(741747911/1000000000 : ℝ)|^79 ≤ (13751040294663/20000000000000 : ℝ)^63
        have hw : |(741747911/1000000000 : ℝ)|=(741747911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-73569883/10000000000 : ℝ)|^79 ≤ (211304918323/100000000000000 : ℝ)^63
        have hw : |(-73569883/10000000000 : ℝ)|=(73569883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(491655671/1250000000 : ℝ)|^79 ≤ (24244916873/78125000000 : ℝ)^63
        have hw : |(491655671/1250000000 : ℝ)|=(491655671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318083_s1_s1_23 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3404150747/10000000000 : ℝ)*x 0 + (6496466231/10000000000 : ℝ)*x 1 + (-2305700107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3404150747/10000000000 : ℝ)^79 ≤ (6472825222251/25000000000000 : ℝ)^63 := by
    have hnat : (3404150747 : ℕ)^79*25000000000000^63 ≤ 6472825222251^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3404150747 10000000000 6472825222251 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6496466231/10000000000 : ℝ)^79 ≤ (29112073661503/50000000000000 : ℝ)^63 := by
    have hnat : (6496466231 : ℕ)^79*50000000000000^63 ≤ 29112073661503^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6496466231 10000000000 29112073661503 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2305700107/10000000000 : ℝ)^79 ≤ (15884551769661/100000000000000 : ℝ)^63 := by
    have hnat : (2305700107 : ℕ)^79*100000000000000^63 ≤ 15884551769661^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305700107 10000000000 15884551769661 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3404150747/10000000000 : ℝ), (6496466231/10000000000 : ℝ), (-2305700107/10000000000 : ℝ)] ![(6472825222251/25000000000000 : ℝ), (29112073661503/50000000000000 : ℝ), (15884551769661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3404150747/10000000000 : ℝ)|^79 ≤ (6472825222251/25000000000000 : ℝ)^63
        have hw : |(3404150747/10000000000 : ℝ)|=(3404150747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6496466231/10000000000 : ℝ)|^79 ≤ (29112073661503/50000000000000 : ℝ)^63
        have hw : |(6496466231/10000000000 : ℝ)|=(6496466231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2305700107/10000000000 : ℝ)|^79 ≤ (15884551769661/100000000000000 : ℝ)^63
        have hw : |(-2305700107/10000000000 : ℝ)|=(2305700107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318083_s1_s1_27 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3295183951/10000000000 : ℝ)*x 0 + (4692001281/10000000000 : ℝ)*x 1 + (446944059/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3295183951/10000000000 : ℝ)^79 ≤ (24856295524651/100000000000000 : ℝ)^63 := by
    have hnat : (3295183951 : ℕ)^79*100000000000000^63 ≤ 24856295524651^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3295183951 10000000000 24856295524651 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4692001281/10000000000 : ℝ)^79 ≤ (2419766920663/6250000000000 : ℝ)^63 := by
    have hnat : (4692001281 : ℕ)^79*6250000000000^63 ≤ 2419766920663^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4692001281 10000000000 2419766920663 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (446944059/1000000000 : ℝ)^79 ≤ (36427433726837/100000000000000 : ℝ)^63 := by
    have hnat : (446944059 : ℕ)^79*100000000000000^63 ≤ 36427433726837^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446944059 1000000000 36427433726837 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3295183951/10000000000 : ℝ), (4692001281/10000000000 : ℝ), (446944059/1000000000 : ℝ)] ![(24856295524651/100000000000000 : ℝ), (2419766920663/6250000000000 : ℝ), (36427433726837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3295183951/10000000000 : ℝ)|^79 ≤ (24856295524651/100000000000000 : ℝ)^63
        have hw : |(3295183951/10000000000 : ℝ)|=(3295183951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4692001281/10000000000 : ℝ)|^79 ≤ (2419766920663/6250000000000 : ℝ)^63
        have hw : |(4692001281/10000000000 : ℝ)|=(4692001281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(446944059/1000000000 : ℝ)|^79 ≤ (36427433726837/100000000000000 : ℝ)^63
        have hw : |(446944059/1000000000 : ℝ)|=(446944059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318083_s1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((65791/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(65791/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((8121/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(8121/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(717/1000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(717/1000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13173/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13173/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((833/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(833/3125 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27943/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27943/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (65791/100000 : ℝ) ^ (39/8 : ℝ) ≤ (12988578602336372657/100000000000000000000 : ℝ) := by
    have hpowers : (65791/100000 : ℝ)^39 ≤ (12988578602336372657/100000000000000000000 : ℝ)^8 := by
      have hnat : (65791 : ℕ)^39*100000000000000000000^8 ≤ 12988578602336372657^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65791 100000 12988578602336372657 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (65791/100000 : ℝ)) (X := (12988578602336372657/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (112988578602336372657/100000000000000000000 : ℝ) ≤ (10253659255269327/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (112988578602336372657/100000000000000000000 : ℝ)^8 ≤ (10253659255269327/10000000000000000 : ℝ)^39 := by
      have hnat : (112988578602336372657 : ℕ)^8*10000000000000000^39 ≤ 10253659255269327^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112988578602336372657 100000000000000000000 10253659255269327 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10253659255269327/10000000000000000 : ℝ)) (X := (112988578602336372657/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (62988578602336372657/50000000000000000000 : ℝ) ≤ (10485102435449757/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (62988578602336372657/50000000000000000000 : ℝ)^8 ≤ (10485102435449757/10000000000000000 : ℝ)^39 := by
      have hnat : (62988578602336372657 : ℕ)^8*10000000000000000^39 ≤ 10485102435449757^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62988578602336372657 50000000000000000000 10485102435449757 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10485102435449757/10000000000000000 : ℝ)) (X := (62988578602336372657/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(253659255269327/6579100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(23144318018043/657910000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (65791/100000 : ℝ)) (alpha := (253659255269327/6579100000000000 : ℝ)) (beta := (23144318018043/657910000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (65791/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(253659255269327/6579100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(23144318018043/657910000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (8121/12500 : ℝ) ^ (39/8 : ℝ) ≤ (381733322148829769/3125000000000000000 : ℝ) := by
    have hpowers : (8121/12500 : ℝ)^39 ≤ (381733322148829769/3125000000000000000 : ℝ)^8 := by
      have hnat : (8121 : ℕ)^39*3125000000000000000^8 ≤ 381733322148829769^8*12500^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8121 12500 381733322148829769 3125000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8121/12500 : ℝ)) (X := (381733322148829769/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (3506733322148829769/3125000000000000000 : ℝ) ≤ (5119614125372333/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3506733322148829769/3125000000000000000 : ℝ)^8 ≤ (5119614125372333/5000000000000000 : ℝ)^39 := by
      have hnat : (3506733322148829769 : ℕ)^8*5000000000000000^39 ≤ 5119614125372333^39*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3506733322148829769 3125000000000000000 5119614125372333 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5119614125372333/5000000000000000 : ℝ)) (X := (3506733322148829769/3125000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (1944233322148829769/1562500000000000000 : ℝ) ≤ (2091714846741947/2000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (1944233322148829769/1562500000000000000 : ℝ)^8 ≤ (2091714846741947/2000000000000000 : ℝ)^39 := by
      have hnat : (1944233322148829769 : ℕ)^8*2000000000000000^39 ≤ 2091714846741947^39*1562500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1944233322148829769 1562500000000000000 2091714846741947 2000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2091714846741947/2000000000000000 : ℝ)) (X := (1944233322148829769/1562500000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(39871375124111/1082800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(73115327655023/2165600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (8121/12500 : ℝ)) (alpha := (39871375124111/1082800000000000 : ℝ)) (beta := (73115327655023/2165600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (8121/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(39871375124111/1082800000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(73115327655023/2165600000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (717/1000 : ℝ) ^ (39/8 : ℝ) ≤ (3950807591024580891/20000000000000000000 : ℝ) := by
    have hpowers : (717/1000 : ℝ)^39 ≤ (3950807591024580891/20000000000000000000 : ℝ)^8 := by
      have hnat : (717 : ℕ)^39*20000000000000000000^8 ≤ 3950807591024580891^8*1000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        717 1000 3950807591024580891 20000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (717/1000 : ℝ)) (X := (3950807591024580891/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (23950807591024580891/20000000000000000000 : ℝ) ≤ (5188353108639461/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (23950807591024580891/20000000000000000000 : ℝ)^8 ≤ (5188353108639461/5000000000000000 : ℝ)^39 := by
      have hnat : (23950807591024580891 : ℕ)^8*5000000000000000^39 ≤ 5188353108639461^39*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23950807591024580891 20000000000000000000 5188353108639461 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5188353108639461/5000000000000000 : ℝ)) (X := (23950807591024580891/20000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (13950807591024580891/10000000000000000000 : ℝ) ≤ (669177642019619/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (13950807591024580891/10000000000000000000 : ℝ)^8 ≤ (669177642019619/625000000000000 : ℝ)^39 := by
      have hnat : (13950807591024580891 : ℕ)^8*625000000000000^39 ≤ 669177642019619^39*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13950807591024580891 10000000000000000000 669177642019619 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (669177642019619/625000000000000 : ℝ)) (X := (13950807591024580891/10000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(62784369546487/1195000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(165068027517491/3585000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (717/1000 : ℝ)) (alpha := (62784369546487/1195000000000000 : ℝ)) (beta := (165068027517491/3585000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (717/1000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(62784369546487/1195000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(165068027517491/3585000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-28404967/125000000 : ℝ)*X 0 0+(18710913/39062500 : ℝ)*X 0 1+(5258921377/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318083_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3375849333/5000000000 : ℝ)*X 1 0+(-824726799/10000000000 : ℝ)*X 1 1+(4281512297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318083_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((887868841/2500000000 : ℝ)*X 2 0+(6366179551/10000000000 : ℝ)*X 2 1+(-115561309/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318083_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2313022507/10000000000 : ℝ)*X 0 0+(950250567/2000000000 : ℝ)*X 0 1+(1052762469/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318083_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((3251284183/5000000000 : ℝ)*X 1 0+(-14620891/2000000000 : ℝ)*X 1 1+(1239726017/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318083_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((624411959/2000000000 : ℝ)*X 2 0+(7191008237/10000000000 : ℝ)*X 2 1+(-418660793/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318083_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((11068101/40000000 : ℝ)*X 0 0+(72817101/156250000 : ℝ)*X 0 1+(4972943587/10000000000 : ℝ)*X 0 2+(11068101/40000000 : ℝ)*X 1 0+(72817101/156250000 : ℝ)*X 1 1+(4972943587/10000000000 : ℝ)*X 1 2+(11068101/40000000 : ℝ)*X 2 0+(72817101/156250000 : ℝ)*X 2 1+(4972943587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318083_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-187344859/1250000000 : ℝ)*X 0 0+(1936383241/5000000000 : ℝ)*X 0 1+(83515653/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318083_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((7699928293/10000000000 : ℝ)*X 1 0+(-32885089/500000000 : ℝ)*X 1 1+(1636736481/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318083_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((363178453/1000000000 : ℝ)*X 2 0+(3416361029/5000000000 : ℝ)*X 2 1+(-790194203/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318083_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2500665521/10000000000 : ℝ)*X 0 0+(387452999/1000000000 : ℝ)*X 0 1+(5932716249/10000000000 : ℝ)*X 0 2+(2500665521/10000000000 : ℝ)*X 1 0+(387452999/1000000000 : ℝ)*X 1 1+(5932716249/10000000000 : ℝ)*X 1 2+(2500665521/10000000000 : ℝ)*X 2 0+(387452999/1000000000 : ℝ)*X 2 1+(5932716249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318083_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-854483467/5000000000 : ℝ)*X 0 0+(2716680121/5000000000 : ℝ)*X 0 1+(5059249541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318083_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((741747911/1000000000 : ℝ)*X 1 0+(-73569883/10000000000 : ℝ)*X 1 1+(491655671/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318083_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((3404150747/10000000000 : ℝ)*X 2 0+(6496466231/10000000000 : ℝ)*X 2 1+(-2305700107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318083_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3295183951/10000000000 : ℝ)*X 0 0+(4692001281/10000000000 : ℝ)*X 0 1+(446944059/1000000000 : ℝ)*X 0 2+(3295183951/10000000000 : ℝ)*X 1 0+(4692001281/10000000000 : ℝ)*X 1 1+(446944059/1000000000 : ℝ)*X 1 2+(3295183951/10000000000 : ℝ)*X 2 0+(4692001281/10000000000 : ℝ)*X 2 1+(446944059/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318083_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((13173/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13173/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (521648022985295071407134931357/42565000643000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8412067/1000000000000 : ℝ)*(base19) + (4881098599/25000000000 : ℝ)*(base40) + (1391301706299/1000000000000 : ℝ)*(base49) + (28849284823/62500000000 : ℝ)*(base60) + (4580236890303/1000000000000 : ℝ)*(major_s1_0) + (4580236890303/1000000000000 : ℝ)*(major_s1_1) + (4580236890303/1000000000000 : ℝ)*(major_s1_2) + (1154320899/1000000000000 : ℝ)*(sp_s1_0) + (14098809/500000000000 : ℝ)*(sp_s1_1) + (1329850537277/200000000000 : ℝ)*(sp_s1_7) + (6650370397599/1000000000000 : ℝ)*(sp_s1_8) + (1662601751821/250000000000 : ℝ)*(sp_s1_9) + (1255012357281/500000000000 : ℝ)*(sp_s1_13) + (37973643/1000000000000 : ℝ)*(sp_s1_20) + (502012537641/200000000000 : ℝ)*(f.failure) + (1662601751821/250000000000 : ℝ)*(f.sum) + (4212032352879301733/12939460000000000000000000000000 : ℝ)*base63 + (255239604960909/1195000000000000000000000000 : ℝ)*base64 + (285771970973913/1082800000000000000000000000 : ℝ)*base67 + (929791301178061/1195000000000000000000000000 : ℝ)*base69 + (42660302521732783069/78620245000000000000000000000000 : ℝ)*base70 + (12979932865067/32895500000000000000000000 : ℝ)*base73 + (251257515228449/2165600000000000000000000000 : ℝ)*base74 + (264679458133779/6579100000000000000000000000 : ℝ)*base76 + (37543601003287100383/71238494800000000000000000000000 : ℝ)*base79 + (741/800000000000000 : ℝ)*base86 + (741/800000000000000 : ℝ)*base88 + (741/800000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((833/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(833/3125 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6403773152140672916123166798607/425650006430000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18188561/1000000000000 : ℝ)*(base21) + (227114204651/250000000000 : ℝ)*(base40) + (73011626549/62500000000 : ℝ)*(base49) + (391852607537/500000000000 : ℝ)*(base60) + (3869881910399/1000000000000 : ℝ)*(major_s1_0) + (3869881910399/1000000000000 : ℝ)*(major_s1_1) + (3869881910399/1000000000000 : ℝ)*(major_s1_2) + (7262191/200000000000 : ℝ)*(sp_s1_1) + (17127539/1000000000000 : ℝ)*(sp_s1_2) + (5618985050369/1000000000000 : ℝ)*(sp_s1_14) + (561889115119/100000000000 : ℝ)*(sp_s1_15) + (5618949734269/1000000000000 : ℝ)*(sp_s1_16) + (265096719441/125000000000 : ℝ)*(sp_s1_20) + (112477/1953125000 : ℝ)*(sp_s1_22) + (265096719441/125000000000 : ℝ)*(f.failure) + (5618985050369/1000000000000 : ℝ)*(f.sum) + (1120656656679215589/12939460000000000000000000000000 : ℝ)*base63 + (574081675924091/3585000000000000000000000000 : ℝ)*base64 + (439060415214671/1082800000000000000000000000 : ℝ)*base66 + (744062324427687/1195000000000000000000000000 : ℝ)*base68 + (65076115437392781431/235860735000000000000000000000000 : ℝ)*base70 + (7606489556793/164477500000000000000000000 : ℝ)*base72 + (412839770853583/2165600000000000000000000000 : ℝ)*base75 + (6277963601528537/6579100000000000000000000000 : ℝ)*base76 + (19996408026336547319/71238494800000000000000000000000 : ℝ)*base79 + (359/500000000000000 : ℝ)*base87 + (359/500000000000000 : ℝ)*base89 + (359/500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27943/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27943/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (668962843117721146359/108280000000000000000000000 : ℝ) := by norm_num
    linear_combination (789332007697/1000000000000 : ℝ)*(base40) + (710522229551/500000000000 : ℝ)*(base49) + (513327/200000000000 : ℝ)*(base50) + (287167/250000000000 : ℝ)*(base60) + (2438476000663/500000000000 : ℝ)*(major_s1_0) + (2438476000663/500000000000 : ℝ)*(major_s1_1) + (2438476000663/500000000000 : ℝ)*(major_s1_2) + (51501881/1000000000000 : ℝ)*(sp_s1_2) + (3971761/125000000000 : ℝ)*(sp_s1_15) + (7771659/200000000000 : ℝ)*(sp_s1_16) + (7081233357821/1000000000000 : ℝ)*(sp_s1_21) + (7081201583733/1000000000000 : ℝ)*(sp_s1_22) + (3540571498823/500000000000 : ℝ)*(sp_s1_23) + (334083573183/125000000000 : ℝ)*(sp_s1_27) + (334083573183/125000000000 : ℝ)*(f.failure) + (7081233357821/1000000000000 : ℝ)*(f.sum) + (65751951255838307/6469730000000000000000000000000 : ℝ)*base62 + (286652462733967/1792500000000000000000000000 : ℝ)*base64 + (130046868402653/541400000000000000000000000 : ℝ)*base67 + (352778030060381/597500000000000000000000000 : ℝ)*base69 + (14570461306343959703/117930367500000000000000000000000 : ℝ)*base71 + (65385480341271/328955000000000000000000000 : ℝ)*base72 + (759379662601049/1082800000000000000000000000 : ℝ)*base74 + (63647023649601/822387500000000000000000000 : ℝ)*base76 + (690646927581978463/35619247400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (283/500000000000000 : ℝ)*base86 + (283/500000000000000 : ℝ)*base88 + (283/500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((65791/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(65791/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((8121/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(8121/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(717/1000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(717/1000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((13173/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13173/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((833/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(833/3125 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27943/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27943/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c318083_s1 p hpa hpb X hX hprev0

#print axioms solution

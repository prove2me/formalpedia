-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312047_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:17:55.324999+00:00
-- url     : https://prove2.me/submissions/983a0be7-5b45-4a16-9da1-e3844a117838

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
theorem collision_support_c312047_s1_s1_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1352701279/10000000000 : ℝ)*x 0 + (-1431567997/2500000000 : ℝ)*x 1 + (5171205937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352701279/10000000000 : ℝ)^37 ≤ (3894964141929/50000000000000 : ℝ)^29 := by
    have hnat : (1352701279 : ℕ)^37*50000000000000^29 ≤ 3894964141929^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352701279 10000000000 3894964141929 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1431567997/2500000000 : ℝ)^37 ≤ (24549804505163/50000000000000 : ℝ)^29 := by
    have hnat : (1431567997 : ℕ)^37*50000000000000^29 ≤ 24549804505163^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1431567997 2500000000 24549804505163 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5171205937/10000000000 : ℝ)^37 ≤ (8622092536741/20000000000000 : ℝ)^29 := by
    have hnat : (5171205937 : ℕ)^37*20000000000000^29 ≤ 8622092536741^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171205937 10000000000 8622092536741 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1352701279/10000000000 : ℝ), (-1431567997/2500000000 : ℝ), (5171205937/10000000000 : ℝ)] ![(3894964141929/50000000000000 : ℝ), (24549804505163/50000000000000 : ℝ), (8622092536741/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1352701279/10000000000 : ℝ)|^37 ≤ (3894964141929/50000000000000 : ℝ)^29
        have hw : |(-1352701279/10000000000 : ℝ)|=(1352701279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1431567997/2500000000 : ℝ)|^37 ≤ (24549804505163/50000000000000 : ℝ)^29
        have hw : |(-1431567997/2500000000 : ℝ)|=(1431567997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5171205937/10000000000 : ℝ)|^37 ≤ (8622092536741/20000000000000 : ℝ)^29
        have hw : |(5171205937/10000000000 : ℝ)|=(5171205937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312047_s1_s1_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1031322657/2000000000 : ℝ)*x 0 + (1966839349/5000000000 : ℝ)*x 1 + (709092077/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031322657/2000000000 : ℝ)^37 ≤ (10738827471199/25000000000000 : ℝ)^29 := by
    have hnat : (1031322657 : ℕ)^37*25000000000000^29 ≤ 10738827471199^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031322657 2000000000 10738827471199 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1966839349/5000000000 : ℝ)^37 ≤ (15205099626799/50000000000000 : ℝ)^29 := by
    have hnat : (1966839349 : ℕ)^37*50000000000000^29 ≤ 15205099626799^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966839349 5000000000 15205099626799 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (709092077/2000000000 : ℝ)^37 ≤ (832327839077/3125000000000 : ℝ)^29 := by
    have hnat : (709092077 : ℕ)^37*3125000000000^29 ≤ 832327839077^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709092077 2000000000 832327839077 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1031322657/2000000000 : ℝ), (1966839349/5000000000 : ℝ), (709092077/2000000000 : ℝ)] ![(10738827471199/25000000000000 : ℝ), (15205099626799/50000000000000 : ℝ), (832327839077/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1031322657/2000000000 : ℝ)|^37 ≤ (10738827471199/25000000000000 : ℝ)^29
        have hw : |(1031322657/2000000000 : ℝ)|=(1031322657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1966839349/5000000000 : ℝ)|^37 ≤ (15205099626799/50000000000000 : ℝ)^29
        have hw : |(1966839349/5000000000 : ℝ)|=(1966839349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(709092077/2000000000 : ℝ)|^37 ≤ (832327839077/3125000000000 : ℝ)^29
        have hw : |(709092077/2000000000 : ℝ)|=(709092077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312047_s1_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5036363277/10000000000 : ℝ)*x 0 + (-4048334717/10000000000 : ℝ)*x 1 + (-3559901407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5036363277/10000000000 : ℝ)^37 ≤ (10420353446001/25000000000000 : ℝ)^29 := by
    have hnat : (5036363277 : ℕ)^37*25000000000000^29 ≤ 10420353446001^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5036363277 10000000000 10420353446001 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4048334717/10000000000 : ℝ)^37 ≤ (31545605770113/100000000000000 : ℝ)^29 := by
    have hnat : (4048334717 : ℕ)^37*100000000000000^29 ≤ 31545605770113^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4048334717 10000000000 31545605770113 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3559901407/10000000000 : ℝ)^37 ≤ (13386490215471/50000000000000 : ℝ)^29 := by
    have hnat : (3559901407 : ℕ)^37*50000000000000^29 ≤ 13386490215471^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3559901407 10000000000 13386490215471 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5036363277/10000000000 : ℝ), (-4048334717/10000000000 : ℝ), (-3559901407/10000000000 : ℝ)] ![(10420353446001/25000000000000 : ℝ), (31545605770113/100000000000000 : ℝ), (13386490215471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5036363277/10000000000 : ℝ)|^37 ≤ (10420353446001/25000000000000 : ℝ)^29
        have hw : |(5036363277/10000000000 : ℝ)|=(5036363277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4048334717/10000000000 : ℝ)|^37 ≤ (31545605770113/100000000000000 : ℝ)^29
        have hw : |(-4048334717/10000000000 : ℝ)|=(4048334717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3559901407/10000000000 : ℝ)|^37 ≤ (13386490215471/50000000000000 : ℝ)^29
        have hw : |(-3559901407/10000000000 : ℝ)|=(3559901407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312047_s1_s1_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6322081203/10000000000 : ℝ)*x 0 + (-1253411873/10000000000 : ℝ)*x 1 + (4609035979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6322081203/10000000000 : ℝ)^37 ≤ (11141788553797/20000000000000 : ℝ)^29 := by
    have hnat : (6322081203 : ℕ)^37*20000000000000^29 ≤ 11141788553797^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6322081203 10000000000 11141788553797 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1253411873/10000000000 : ℝ)^37 ≤ (3533963823643/50000000000000 : ℝ)^29 := by
    have hnat : (1253411873 : ℕ)^37*50000000000000^29 ≤ 3533963823643^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253411873 10000000000 3533963823643 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4609035979/10000000000 : ℝ)^37 ≤ (37223129571271/100000000000000 : ℝ)^29 := by
    have hnat : (4609035979 : ℕ)^37*100000000000000^29 ≤ 37223129571271^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4609035979 10000000000 37223129571271 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6322081203/10000000000 : ℝ), (-1253411873/10000000000 : ℝ), (4609035979/10000000000 : ℝ)] ![(11141788553797/20000000000000 : ℝ), (3533963823643/50000000000000 : ℝ), (37223129571271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6322081203/10000000000 : ℝ)|^37 ≤ (11141788553797/20000000000000 : ℝ)^29
        have hw : |(6322081203/10000000000 : ℝ)|=(6322081203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1253411873/10000000000 : ℝ)|^37 ≤ (3533963823643/50000000000000 : ℝ)^29
        have hw : |(-1253411873/10000000000 : ℝ)|=(1253411873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4609035979/10000000000 : ℝ)|^37 ≤ (37223129571271/100000000000000 : ℝ)^29
        have hw : |(4609035979/10000000000 : ℝ)|=(4609035979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312047_s1_s1_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073035173/10000000000 : ℝ)*x 0 + (-24797793/39062500 : ℝ)*x 1 + (2351784147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073035173/10000000000 : ℝ)^37 ≤ (5796917487627/100000000000000 : ℝ)^29 := by
    have hnat : (1073035173 : ℕ)^37*100000000000000^29 ≤ 5796917487627^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073035173 10000000000 5796917487627 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24797793/39062500 : ℝ)^37 ≤ (7000393547237/12500000000000 : ℝ)^29 := by
    have hnat : (24797793 : ℕ)^37*12500000000000^29 ≤ 7000393547237^29*39062500^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24797793 39062500 7000393547237 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2351784147/5000000000 : ℝ)^37 ≤ (4774991765547/12500000000000 : ℝ)^29 := by
    have hnat : (2351784147 : ℕ)^37*12500000000000^29 ≤ 4774991765547^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351784147 5000000000 4774991765547 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073035173/10000000000 : ℝ), (-24797793/39062500 : ℝ), (2351784147/5000000000 : ℝ)] ![(5796917487627/100000000000000 : ℝ), (7000393547237/12500000000000 : ℝ), (4774991765547/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073035173/10000000000 : ℝ)|^37 ≤ (5796917487627/100000000000000 : ℝ)^29
        have hw : |(-1073035173/10000000000 : ℝ)|=(1073035173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24797793/39062500 : ℝ)|^37 ≤ (7000393547237/12500000000000 : ℝ)^29
        have hw : |(-24797793/39062500 : ℝ)|=(24797793/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2351784147/5000000000 : ℝ)|^37 ≤ (4774991765547/12500000000000 : ℝ)^29
        have hw : |(2351784147/5000000000 : ℝ)|=(2351784147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312047_s1_s1_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4985401973/10000000000 : ℝ)*x 0 + (243309913/625000000 : ℝ)*x 1 + (3774273179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4985401973/10000000000 : ℝ)^37 ≤ (41144058401889/100000000000000 : ℝ)^29 := by
    have hnat : (4985401973 : ℕ)^37*100000000000000^29 ≤ 41144058401889^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4985401973 10000000000 41144058401889 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243309913/625000000 : ℝ)^37 ≤ (6001827593263/20000000000000 : ℝ)^29 := by
    have hnat : (243309913 : ℕ)^37*20000000000000^29 ≤ 6001827593263^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243309913 625000000 6001827593263 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3774273179/10000000000 : ℝ)^37 ≤ (28846803619749/100000000000000 : ℝ)^29 := by
    have hnat : (3774273179 : ℕ)^37*100000000000000^29 ≤ 28846803619749^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3774273179 10000000000 28846803619749 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4985401973/10000000000 : ℝ), (243309913/625000000 : ℝ), (3774273179/10000000000 : ℝ)] ![(41144058401889/100000000000000 : ℝ), (6001827593263/20000000000000 : ℝ), (28846803619749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4985401973/10000000000 : ℝ)|^37 ≤ (41144058401889/100000000000000 : ℝ)^29
        have hw : |(4985401973/10000000000 : ℝ)|=(4985401973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(243309913/625000000 : ℝ)|^37 ≤ (6001827593263/20000000000000 : ℝ)^29
        have hw : |(243309913/625000000 : ℝ)|=(243309913/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3774273179/10000000000 : ℝ)|^37 ≤ (28846803619749/100000000000000 : ℝ)^29
        have hw : |(3774273179/10000000000 : ℝ)|=(3774273179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312047_s1_s1_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5167614653/10000000000 : ℝ)*x 0 + (-3818766293/10000000000 : ℝ)*x 1 + (-1825302347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5167614653/10000000000 : ℝ)^37 ≤ (43072268017637/100000000000000 : ℝ)^29 := by
    have hnat : (5167614653 : ℕ)^37*100000000000000^29 ≤ 43072268017637^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167614653 10000000000 43072268017637 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3818766293/10000000000 : ℝ)^37 ≤ (29281378371251/100000000000000 : ℝ)^29 := by
    have hnat : (3818766293 : ℕ)^37*100000000000000^29 ≤ 29281378371251^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3818766293 10000000000 29281378371251 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1825302347/5000000000 : ℝ)^37 ≤ (13823176798129/50000000000000 : ℝ)^29 := by
    have hnat : (1825302347 : ℕ)^37*50000000000000^29 ≤ 13823176798129^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1825302347 5000000000 13823176798129 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5167614653/10000000000 : ℝ), (-3818766293/10000000000 : ℝ), (-1825302347/5000000000 : ℝ)] ![(43072268017637/100000000000000 : ℝ), (29281378371251/100000000000000 : ℝ), (13823176798129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5167614653/10000000000 : ℝ)|^37 ≤ (43072268017637/100000000000000 : ℝ)^29
        have hw : |(5167614653/10000000000 : ℝ)|=(5167614653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3818766293/10000000000 : ℝ)|^37 ≤ (29281378371251/100000000000000 : ℝ)^29
        have hw : |(-3818766293/10000000000 : ℝ)|=(3818766293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1825302347/5000000000 : ℝ)|^37 ≤ (13823176798129/50000000000000 : ℝ)^29
        have hw : |(-1825302347/5000000000 : ℝ)|=(1825302347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312047_s1_s1_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6368586637/10000000000 : ℝ)*x 0 + (-506745553/10000000000 : ℝ)*x 1 + (5023142157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6368586637/10000000000 : ℝ)^37 ≤ (56232316496791/100000000000000 : ℝ)^29 := by
    have hnat : (6368586637 : ℕ)^37*100000000000000^29 ≤ 56232316496791^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6368586637 10000000000 56232316496791 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506745553/10000000000 : ℝ)^37 ≤ (4347310499/195312500000 : ℝ)^29 := by
    have hnat : (506745553 : ℕ)^37*195312500000^29 ≤ 4347310499^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506745553 10000000000 4347310499 195312500000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5023142157/10000000000 : ℝ)^37 ≤ (10385465131079/25000000000000 : ℝ)^29 := by
    have hnat : (5023142157 : ℕ)^37*25000000000000^29 ≤ 10385465131079^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5023142157 10000000000 10385465131079 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6368586637/10000000000 : ℝ), (-506745553/10000000000 : ℝ), (5023142157/10000000000 : ℝ)] ![(56232316496791/100000000000000 : ℝ), (4347310499/195312500000 : ℝ), (10385465131079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6368586637/10000000000 : ℝ)|^37 ≤ (56232316496791/100000000000000 : ℝ)^29
        have hw : |(6368586637/10000000000 : ℝ)|=(6368586637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-506745553/10000000000 : ℝ)|^37 ≤ (4347310499/195312500000 : ℝ)^29
        have hw : |(-506745553/10000000000 : ℝ)|=(506745553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5023142157/10000000000 : ℝ)|^37 ≤ (10385465131079/25000000000000 : ℝ)^29
        have hw : |(5023142157/10000000000 : ℝ)|=(5023142157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312047_s1_s1_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-20844269/250000000 : ℝ)*x 0 + (-5544786851/10000000000 : ℝ)*x 1 + (5687473427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20844269/250000000 : ℝ)^37 ≤ (420149992361/10000000000000 : ℝ)^29 := by
    have hnat : (20844269 : ℕ)^37*10000000000000^29 ≤ 420149992361^29*250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20844269 250000000 420149992361 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5544786851/10000000000 : ℝ)^37 ≤ (47122942621501/100000000000000 : ℝ)^29 := by
    have hnat : (5544786851 : ℕ)^37*100000000000000^29 ≤ 47122942621501^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5544786851 10000000000 47122942621501 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5687473427/10000000000 : ℝ)^37 ≤ (24337778719453/50000000000000 : ℝ)^29 := by
    have hnat : (5687473427 : ℕ)^37*50000000000000^29 ≤ 24337778719453^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5687473427 10000000000 24337778719453 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-20844269/250000000 : ℝ), (-5544786851/10000000000 : ℝ), (5687473427/10000000000 : ℝ)] ![(420149992361/10000000000000 : ℝ), (47122942621501/100000000000000 : ℝ), (24337778719453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-20844269/250000000 : ℝ)|^37 ≤ (420149992361/10000000000000 : ℝ)^29
        have hw : |(-20844269/250000000 : ℝ)|=(20844269/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5544786851/10000000000 : ℝ)|^37 ≤ (47122942621501/100000000000000 : ℝ)^29
        have hw : |(-5544786851/10000000000 : ℝ)|=(5544786851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5687473427/10000000000 : ℝ)|^37 ≤ (24337778719453/50000000000000 : ℝ)^29
        have hw : |(5687473427/10000000000 : ℝ)|=(5687473427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312047_s1_s1_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (984911697/2000000000 : ℝ)*x 0 + (4116564733/10000000000 : ℝ)*x 1 + (3611596869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (984911697/2000000000 : ℝ)^37 ≤ (1265765132107/3125000000000 : ℝ)^29 := by
    have hnat : (984911697 : ℕ)^37*3125000000000^29 ≤ 1265765132107^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984911697 2000000000 1265765132107 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4116564733/10000000000 : ℝ)^37 ≤ (32225507285141/100000000000000 : ℝ)^29 := by
    have hnat : (4116564733 : ℕ)^37*100000000000000^29 ≤ 32225507285141^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116564733 10000000000 32225507285141 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3611596869/10000000000 : ℝ)^37 ≤ (2727000846623/10000000000000 : ℝ)^29 := by
    have hnat : (3611596869 : ℕ)^37*10000000000000^29 ≤ 2727000846623^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3611596869 10000000000 2727000846623 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(984911697/2000000000 : ℝ), (4116564733/10000000000 : ℝ), (3611596869/10000000000 : ℝ)] ![(1265765132107/3125000000000 : ℝ), (32225507285141/100000000000000 : ℝ), (2727000846623/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(984911697/2000000000 : ℝ)|^37 ≤ (1265765132107/3125000000000 : ℝ)^29
        have hw : |(984911697/2000000000 : ℝ)|=(984911697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4116564733/10000000000 : ℝ)|^37 ≤ (32225507285141/100000000000000 : ℝ)^29
        have hw : |(4116564733/10000000000 : ℝ)|=(4116564733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3611596869/10000000000 : ℝ)|^37 ≤ (2727000846623/10000000000000 : ℝ)^29
        have hw : |(3611596869/10000000000 : ℝ)|=(3611596869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312047_s1_s1_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (174074179/312500000 : ℝ)*x 0 + (-3787685331/10000000000 : ℝ)*x 1 + (-3227101917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174074179/312500000 : ℝ)^37 ≤ (5925069835077/12500000000000 : ℝ)^29 := by
    have hnat : (174074179 : ℕ)^37*12500000000000^29 ≤ 5925069835077^29*312500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174074179 312500000 5925069835077 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3787685331/10000000000 : ℝ)^37 ≤ (14488827633483/50000000000000 : ℝ)^29 := by
    have hnat : (3787685331 : ℕ)^37*50000000000000^29 ≤ 14488827633483^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3787685331 10000000000 14488827633483 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3227101917/10000000000 : ℝ)^37 ≤ (11810893016907/50000000000000 : ℝ)^29 := by
    have hnat : (3227101917 : ℕ)^37*50000000000000^29 ≤ 11810893016907^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3227101917 10000000000 11810893016907 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174074179/312500000 : ℝ), (-3787685331/10000000000 : ℝ), (-3227101917/10000000000 : ℝ)] ![(5925069835077/12500000000000 : ℝ), (14488827633483/50000000000000 : ℝ), (11810893016907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174074179/312500000 : ℝ)|^37 ≤ (5925069835077/12500000000000 : ℝ)^29
        have hw : |(174074179/312500000 : ℝ)|=(174074179/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3787685331/10000000000 : ℝ)|^37 ≤ (14488827633483/50000000000000 : ℝ)^29
        have hw : |(-3787685331/10000000000 : ℝ)|=(3787685331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3227101917/10000000000 : ℝ)|^37 ≤ (11810893016907/50000000000000 : ℝ)^29
        have hw : |(-3227101917/10000000000 : ℝ)|=(3227101917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312047_s1_s1_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (172328679/250000000 : ℝ)*x 0 + (-1073569037/10000000000 : ℝ)*x 1 + (2046576241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172328679/250000000 : ℝ)^37 ≤ (15551886928137/25000000000000 : ℝ)^29 := by
    have hnat : (172328679 : ℕ)^37*25000000000000^29 ≤ 15551886928137^29*250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172328679 250000000 15551886928137 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073569037/10000000000 : ℝ)^37 ≤ (725074685427/12500000000000 : ℝ)^29 := by
    have hnat : (1073569037 : ℕ)^37*12500000000000^29 ≤ 725074685427^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073569037 10000000000 725074685427 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2046576241/5000000000 : ℝ)^37 ≤ (3998981848821/12500000000000 : ℝ)^29 := by
    have hnat : (2046576241 : ℕ)^37*12500000000000^29 ≤ 3998981848821^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046576241 5000000000 3998981848821 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172328679/250000000 : ℝ), (-1073569037/10000000000 : ℝ), (2046576241/5000000000 : ℝ)] ![(15551886928137/25000000000000 : ℝ), (725074685427/12500000000000 : ℝ), (3998981848821/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172328679/250000000 : ℝ)|^37 ≤ (15551886928137/25000000000000 : ℝ)^29
        have hw : |(172328679/250000000 : ℝ)|=(172328679/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1073569037/10000000000 : ℝ)|^37 ≤ (725074685427/12500000000000 : ℝ)^29
        have hw : |(-1073569037/10000000000 : ℝ)|=(1073569037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2046576241/5000000000 : ℝ)|^37 ≤ (3998981848821/12500000000000 : ℝ)^29
        have hw : |(2046576241/5000000000 : ℝ)|=(2046576241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312047_s1_s1_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-749338051/10000000000 : ℝ)*x 0 + (-1252282327/2000000000 : ℝ)*x 1 + (1250189113/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (749338051/10000000000 : ℝ)^37 ≤ (3666435694437/100000000000000 : ℝ)^29 := by
    have hnat : (749338051 : ℕ)^37*100000000000000^29 ≤ 3666435694437^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749338051 10000000000 3666435694437 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1252282327/2000000000 : ℝ)^37 ≤ (11005552235653/20000000000000 : ℝ)^29 := by
    have hnat : (1252282327 : ℕ)^37*20000000000000^29 ≤ 11005552235653^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252282327 2000000000 11005552235653 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1250189113/2500000000 : ℝ)^37 ≤ (41305803107927/100000000000000 : ℝ)^29 := by
    have hnat : (1250189113 : ℕ)^37*100000000000000^29 ≤ 41305803107927^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250189113 2500000000 41305803107927 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-749338051/10000000000 : ℝ), (-1252282327/2000000000 : ℝ), (1250189113/2500000000 : ℝ)] ![(3666435694437/100000000000000 : ℝ), (11005552235653/20000000000000 : ℝ), (41305803107927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-749338051/10000000000 : ℝ)|^37 ≤ (3666435694437/100000000000000 : ℝ)^29
        have hw : |(-749338051/10000000000 : ℝ)|=(749338051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1252282327/2000000000 : ℝ)|^37 ≤ (11005552235653/20000000000000 : ℝ)^29
        have hw : |(-1252282327/2000000000 : ℝ)|=(1252282327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1250189113/2500000000 : ℝ)|^37 ≤ (41305803107927/100000000000000 : ℝ)^29
        have hw : |(1250189113/2500000000 : ℝ)|=(1250189113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312047_s1_s1_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5720549921/10000000000 : ℝ)*x 0 + (3576285679/10000000000 : ℝ)*x 1 + (3271017813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5720549921/10000000000 : ℝ)^37 ≤ (49037019313353/100000000000000 : ℝ)^29 := by
    have hnat : (5720549921 : ℕ)^37*100000000000000^29 ≤ 49037019313353^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5720549921 10000000000 49037019313353 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3576285679/10000000000 : ℝ)^37 ≤ (33662866933/125000000000 : ℝ)^29 := by
    have hnat : (3576285679 : ℕ)^37*125000000000^29 ≤ 33662866933^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3576285679 10000000000 33662866933 125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3271017813/10000000000 : ℝ)^37 ≤ (12016343558611/50000000000000 : ℝ)^29 := by
    have hnat : (3271017813 : ℕ)^37*50000000000000^29 ≤ 12016343558611^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3271017813 10000000000 12016343558611 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5720549921/10000000000 : ℝ), (3576285679/10000000000 : ℝ), (3271017813/10000000000 : ℝ)] ![(49037019313353/100000000000000 : ℝ), (33662866933/125000000000 : ℝ), (12016343558611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5720549921/10000000000 : ℝ)|^37 ≤ (49037019313353/100000000000000 : ℝ)^29
        have hw : |(5720549921/10000000000 : ℝ)|=(5720549921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3576285679/10000000000 : ℝ)|^37 ≤ (33662866933/125000000000 : ℝ)^29
        have hw : |(3576285679/10000000000 : ℝ)|=(3576285679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3271017813/10000000000 : ℝ)|^37 ≤ (12016343558611/50000000000000 : ℝ)^29
        have hw : |(3271017813/10000000000 : ℝ)|=(3271017813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312047_s1_s1_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4860947439/10000000000 : ℝ)*x 0 + (-4135444119/10000000000 : ℝ)*x 1 + (-3661085891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4860947439/10000000000 : ℝ)^37 ≤ (7967629061647/20000000000000 : ℝ)^29 := by
    have hnat : (4860947439 : ℕ)^37*20000000000000^29 ≤ 7967629061647^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4860947439 10000000000 7967629061647 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4135444119/10000000000 : ℝ)^37 ≤ (32414189402481/100000000000000 : ℝ)^29 := by
    have hnat : (4135444119 : ℕ)^37*100000000000000^29 ≤ 32414189402481^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135444119 10000000000 32414189402481 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3661085891/10000000000 : ℝ)^37 ≤ (13873832635337/50000000000000 : ℝ)^29 := by
    have hnat : (3661085891 : ℕ)^37*50000000000000^29 ≤ 13873832635337^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3661085891 10000000000 13873832635337 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4860947439/10000000000 : ℝ), (-4135444119/10000000000 : ℝ), (-3661085891/10000000000 : ℝ)] ![(7967629061647/20000000000000 : ℝ), (32414189402481/100000000000000 : ℝ), (13873832635337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4860947439/10000000000 : ℝ)|^37 ≤ (7967629061647/20000000000000 : ℝ)^29
        have hw : |(4860947439/10000000000 : ℝ)|=(4860947439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4135444119/10000000000 : ℝ)|^37 ≤ (32414189402481/100000000000000 : ℝ)^29
        have hw : |(-4135444119/10000000000 : ℝ)|=(4135444119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3661085891/10000000000 : ℝ)|^37 ≤ (13873832635337/50000000000000 : ℝ)^29
        have hw : |(-3661085891/10000000000 : ℝ)|=(3661085891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312047_s1_s1_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (861020133/1250000000 : ℝ)*x 0 + (-177440671/2500000000 : ℝ)*x 1 + (4335562359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861020133/1250000000 : ℝ)^37 ≤ (62150143131273/100000000000000 : ℝ)^29 := by
    have hnat : (861020133 : ℕ)^37*100000000000000^29 ≤ 62150143131273^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861020133 1250000000 62150143131273 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177440671/2500000000 : ℝ)^37 ≤ (1710601571847/50000000000000 : ℝ)^29 := by
    have hnat : (177440671 : ℕ)^37*50000000000000^29 ≤ 1710601571847^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177440671 2500000000 1710601571847 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4335562359/10000000000 : ℝ)^37 ≤ (34428653708387/100000000000000 : ℝ)^29 := by
    have hnat : (4335562359 : ℕ)^37*100000000000000^29 ≤ 34428653708387^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335562359 10000000000 34428653708387 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861020133/1250000000 : ℝ), (-177440671/2500000000 : ℝ), (4335562359/10000000000 : ℝ)] ![(62150143131273/100000000000000 : ℝ), (1710601571847/50000000000000 : ℝ), (34428653708387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861020133/1250000000 : ℝ)|^37 ≤ (62150143131273/100000000000000 : ℝ)^29
        have hw : |(861020133/1250000000 : ℝ)|=(861020133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-177440671/2500000000 : ℝ)|^37 ≤ (1710601571847/50000000000000 : ℝ)^29
        have hw : |(-177440671/2500000000 : ℝ)|=(177440671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4335562359/10000000000 : ℝ)|^37 ≤ (34428653708387/100000000000000 : ℝ)^29
        have hw : |(4335562359/10000000000 : ℝ)|=(4335562359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312047_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((73909/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73909/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64829/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-64829/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83759/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(83759/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((17103/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17103/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17553/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-17553/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(771/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(771/2500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (73909/100000 : ℝ) ^ (9/2 : ℝ) ≤ (12826494298794890697/50000000000000000000 : ℝ) := by
    have hpowers : (73909/100000 : ℝ)^9 ≤ (12826494298794890697/50000000000000000000 : ℝ)^2 := by
      have hnat : (73909 : ℕ)^9*50000000000000000000^2 ≤ 12826494298794890697^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73909 100000 12826494298794890697 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73909/100000 : ℝ)) (X := (12826494298794890697/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (62826494298794890697/50000000000000000000 : ℝ) ≤ (10520549037690323/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (62826494298794890697/50000000000000000000 : ℝ)^2 ≤ (10520549037690323/10000000000000000 : ℝ)^9 := by
      have hnat : (62826494298794890697 : ℕ)^2*10000000000000000^9 ≤ 10520549037690323^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62826494298794890697 50000000000000000000 10520549037690323 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10520549037690323/10000000000000000 : ℝ)) (X := (62826494298794890697/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (37826494298794890697/25000000000000000000 : ℝ) ≤ (10963974551617753/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (37826494298794890697/25000000000000000000 : ℝ)^2 ≤ (10963974551617753/10000000000000000 : ℝ)^9 := by
      have hnat : (37826494298794890697 : ℕ)^2*10000000000000000^9 ≤ 10963974551617753^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37826494298794890697 25000000000000000000 10963974551617753 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10963974551617753/10000000000000000 : ℝ)) (X := (37826494298794890697/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(520549037690323/7390900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(44342551392743/739090000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (73909/100000 : ℝ)) (alpha := (520549037690323/7390900000000000 : ℝ)) (beta := (44342551392743/739090000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (73909/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(520549037690323/7390900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(44342551392743/739090000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (64829/100000 : ℝ) ^ (9/2 : ℝ) ≤ (14222041828058045329/100000000000000000000 : ℝ) := by
    have hpowers : (64829/100000 : ℝ)^9 ≤ (14222041828058045329/100000000000000000000 : ℝ)^2 := by
      have hnat : (64829 : ℕ)^9*100000000000000000000^2 ≤ 14222041828058045329^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64829 100000 14222041828058045329 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64829/100000 : ℝ)) (X := (14222041828058045329/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (114222041828058045329/100000000000000000000 : ℝ) ≤ (51499536425137/50000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (114222041828058045329/100000000000000000000 : ℝ)^2 ≤ (51499536425137/50000000000000 : ℝ)^9 := by
      have hnat : (114222041828058045329 : ℕ)^2*50000000000000^9 ≤ 51499536425137^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        114222041828058045329 100000000000000000000 51499536425137 50000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (51499536425137/50000000000000 : ℝ)) (X := (114222041828058045329/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (64222041828058045329/50000000000000000000 : ℝ) ≤ (2114407475654097/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (64222041828058045329/50000000000000000000 : ℝ)^2 ≤ (2114407475654097/2000000000000000 : ℝ)^9 := by
      have hnat : (64222041828058045329 : ℕ)^2*2000000000000000^9 ≤ 2114407475654097^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64222041828058045329 50000000000000000000 2114407475654097 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2114407475654097/2000000000000000 : ℝ)) (X := (64222041828058045329/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1499536425137/32414500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(54426018648617/1296580000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (64829/100000 : ℝ)) (alpha := (1499536425137/32414500000000 : ℝ)) (beta := (54426018648617/1296580000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (64829/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1499536425137/32414500000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(54426018648617/1296580000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (83759/100000 : ℝ) ^ (9/2 : ℝ) ≤ (45044490238505300063/100000000000000000000 : ℝ) := by
    have hpowers : (83759/100000 : ℝ)^9 ≤ (45044490238505300063/100000000000000000000 : ℝ)^2 := by
      have hnat : (83759 : ℕ)^9*100000000000000000000^2 ≤ 45044490238505300063^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83759 100000 45044490238505300063 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (83759/100000 : ℝ)) (X := (45044490238505300063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (145044490238505300063/100000000000000000000 : ℝ) ≤ (10861483919579211/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (145044490238505300063/100000000000000000000 : ℝ)^2 ≤ (10861483919579211/10000000000000000 : ℝ)^9 := by
      have hnat : (145044490238505300063 : ℕ)^2*10000000000000000^9 ≤ 10861483919579211^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        145044490238505300063 100000000000000000000 10861483919579211 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10861483919579211/10000000000000000 : ℝ)) (X := (145044490238505300063/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (95044490238505300063/50000000000000000000 : ℝ) ≤ (2306855689361357/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (95044490238505300063/50000000000000000000 : ℝ)^2 ≤ (2306855689361357/2000000000000000 : ℝ)^9 := by
      have hnat : (95044490238505300063 : ℕ)^2*2000000000000000^9 ≤ 2306855689361357^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        95044490238505300063 50000000000000000000 2306855689361357 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2306855689361357/2000000000000000 : ℝ)) (X := (95044490238505300063/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(861483919579211/8375900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(336397263613787/4187950000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (83759/100000 : ℝ)) (alpha := (861483919579211/8375900000000000 : ℝ)) (beta := (336397263613787/4187950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (83759/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(861483919579211/8375900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(336397263613787/4187950000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1352701279/10000000000 : ℝ)*X 0 0+(-1431567997/2500000000 : ℝ)*X 0 1+(5171205937/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1031322657/2000000000 : ℝ)*X 1 0+(1966839349/5000000000 : ℝ)*X 1 1+(709092077/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5036363277/10000000000 : ℝ)*X 2 0+(-4048334717/10000000000 : ℝ)*X 2 1+(-3559901407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6322081203/10000000000 : ℝ)*X 0 0+(-1253411873/10000000000 : ℝ)*X 0 1+(4609035979/10000000000 : ℝ)*X 0 2+(6322081203/10000000000 : ℝ)*X 1 0+(-1253411873/10000000000 : ℝ)*X 1 1+(4609035979/10000000000 : ℝ)*X 1 2+(6322081203/10000000000 : ℝ)*X 2 0+(-1253411873/10000000000 : ℝ)*X 2 1+(4609035979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1073035173/10000000000 : ℝ)*X 0 0+(-24797793/39062500 : ℝ)*X 0 1+(2351784147/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4985401973/10000000000 : ℝ)*X 1 0+(243309913/625000000 : ℝ)*X 1 1+(3774273179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5167614653/10000000000 : ℝ)*X 2 0+(-3818766293/10000000000 : ℝ)*X 2 1+(-1825302347/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((6368586637/10000000000 : ℝ)*X 0 0+(-506745553/10000000000 : ℝ)*X 0 1+(5023142157/10000000000 : ℝ)*X 0 2+(6368586637/10000000000 : ℝ)*X 1 0+(-506745553/10000000000 : ℝ)*X 1 1+(5023142157/10000000000 : ℝ)*X 1 2+(6368586637/10000000000 : ℝ)*X 2 0+(-506745553/10000000000 : ℝ)*X 2 1+(5023142157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-20844269/250000000 : ℝ)*X 0 0+(-5544786851/10000000000 : ℝ)*X 0 1+(5687473427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((984911697/2000000000 : ℝ)*X 1 0+(4116564733/10000000000 : ℝ)*X 1 1+(3611596869/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((174074179/312500000 : ℝ)*X 2 0+(-3787685331/10000000000 : ℝ)*X 2 1+(-3227101917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((172328679/250000000 : ℝ)*X 0 0+(-1073569037/10000000000 : ℝ)*X 0 1+(2046576241/5000000000 : ℝ)*X 0 2+(172328679/250000000 : ℝ)*X 1 0+(-1073569037/10000000000 : ℝ)*X 1 1+(2046576241/5000000000 : ℝ)*X 1 2+(172328679/250000000 : ℝ)*X 2 0+(-1073569037/10000000000 : ℝ)*X 2 1+(2046576241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-749338051/10000000000 : ℝ)*X 0 0+(-1252282327/2000000000 : ℝ)*X 0 1+(1250189113/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5720549921/10000000000 : ℝ)*X 1 0+(3576285679/10000000000 : ℝ)*X 1 1+(3271017813/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4860947439/10000000000 : ℝ)*X 2 0+(-4135444119/10000000000 : ℝ)*X 2 1+(-3661085891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((861020133/1250000000 : ℝ)*X 0 0+(-177440671/2500000000 : ℝ)*X 0 1+(4335562359/10000000000 : ℝ)*X 0 2+(861020133/1250000000 : ℝ)*X 1 0+(-177440671/2500000000 : ℝ)*X 1 1+(4335562359/10000000000 : ℝ)*X 1 2+(861020133/1250000000 : ℝ)*X 2 0+(-177440671/2500000000 : ℝ)*X 2 1+(4335562359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312047_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((17103/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17103/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17536915556924389336678119107937/1824212602285450000000000000000000000 : ℝ) := by norm_num
    linear_combination (1719854699553/1000000000000 : ℝ)*(base40) + (306588734059/500000000000 : ℝ)*(base50) + (6788801/1000000000000 : ℝ)*(base59) + (933398697407/125000000000 : ℝ)*(major_s1_0) + (933398697407/125000000000 : ℝ)*(major_s1_1) + (933398697407/125000000000 : ℝ)*(major_s1_2) + (5587593/20000000000 : ℝ)*(sp_s1_0) + (87720433/500000000000 : ℝ)*(sp_s1_6) + (10460394957817/1000000000000 : ℝ)*(sp_s1_7) + (209209260011/20000000000 : ℝ)*(sp_s1_8) + (2615092093863/250000000000 : ℝ)*(sp_s1_9) + (4473526175699/1000000000000 : ℝ)*(sp_s1_13) + (211336917/1000000000000 : ℝ)*(sp_s1_15) + (152981007/500000000000 : ℝ)*(sp_s1_23) + (1118425404141/250000000000 : ℝ)*(f.failure) + (10460674337467/1000000000000 : ℝ)*(f.sum) + (47666862973788677709/135750305275000000000000000000000 : ℝ)*base62 + (1755797824759767/4187950000000000000000000000 : ℝ)*base65 + (333690334326869/648290000000000000000000000 : ℝ)*base66 + (292625985023689/523493750000000000000000000 : ℝ)*base68 + (879525159574867189/1758677253125000000000000000000 : ℝ)*base71 + (3166292460737/4199375000000000000000000 : ℝ)*base72 + (3824865395487/648290000000000000000000000 : ℝ)*base74 + (28102187794669/335950000000000000000000000 : ℝ)*base77 + (4300662149344607589/4355860510000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (13267/25000000000000000 : ℝ)*base86 + (13267/25000000000000000 : ℝ)*base88 + (13267/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17553/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-17553/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (27780414361742269801717071804189/1824212602285450000000000000000000000 : ℝ) := by norm_num
    linear_combination (1049986181761/500000000000 : ℝ)*(base40) + (89726341171/250000000000 : ℝ)*(base59) + (6799879470989/1000000000000 : ℝ)*(major_s1_0) + (6799879470989/1000000000000 : ℝ)*(major_s1_1) + (6799879470989/1000000000000 : ℝ)*(major_s1_2) + (6153611/100000000000 : ℝ)*(sp_s1_0) + (140467897/500000000000 : ℝ)*(sp_s1_1) + (26442573/250000000000 : ℝ)*(sp_s1_6) + (331891749/1000000000000 : ℝ)*(sp_s1_8) + (2381446470191/250000000000 : ℝ)*(sp_s1_14) + (952523458933/100000000000 : ℝ)*(sp_s1_15) + (4762923708437/500000000000 : ℝ)*(sp_s1_16) + (1018444289319/250000000000 : ℝ)*(sp_s1_20) + (11760647/500000000000 : ℝ)*(sp_s1_27) + (2036953224431/500000000000 : ℝ)*(f.failure) + (4762923708437/500000000000 : ℝ)*(f.sum) + (57942332392953651871/543001221100000000000000000000000 : ℝ)*base63 + (12034023333403/4187950000000000000000000000 : ℝ)*base65 + (521530094973339/1296580000000000000000000000 : ℝ)*base66 + (1228865492768969/8375900000000000000000000000 : ℝ)*base69 + (10863846645156555377/56277672100000000000000000000000 : ℝ)*base71 + (11859500869603/33595000000000000000000000 : ℝ)*base72 + (26691427027567/81036250000000000000000000 : ℝ)*base74 + (507159246737097/671900000000000000000000000 : ℝ)*base77 + (2167218131258513523/8711721020000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1503/50000000000000000 : ℝ)*base87 + (1503/50000000000000000 : ℝ)*base89 + (1503/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(771/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(771/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (542060468357460225708057513/47914465610000000000000000000000 : ℝ) := by norm_num
    linear_combination (2767007644193/1000000000000 : ℝ)*(base40) + (213029608703/500000000000 : ℝ)*(base50) + (449602142519/50000000000 : ℝ)*(major_s1_0) + (449602142519/50000000000 : ℝ)*(major_s1_1) + (449602142519/50000000000 : ℝ)*(major_s1_2) + (45166639/500000000000 : ℝ)*(sp_s1_0) + (143247147/1000000000000 : ℝ)*(sp_s1_1) + (124711343/500000000000 : ℝ)*(sp_s1_2) + (35402911/500000000000 : ℝ)*(sp_s1_7) + (87159967/500000000000 : ℝ)*(sp_s1_20) + (12596657455607/1000000000000 : ℝ)*(sp_s1_21) + (314916883689/25000000000 : ℝ)*(sp_s1_22) + (629828458601/50000000000 : ℝ)*(sp_s1_23) + (1077417803017/200000000000 : ℝ)*(sp_s1_27) + (5387263335019/1000000000000 : ℝ)*(f.failure) + (12596818594707/1000000000000 : ℝ)*(f.sum) + (19227392416274494017/54300122110000000000000000000000 : ℝ)*base63 + (498592702845509/837590000000000000000000000 : ℝ)*base65 + (602659157207979/648290000000000000000000000 : ℝ)*base66 + (514052505718047/837590000000000000000000000 : ℝ)*base68 + (8696551841680973857/30952719655000000000000000000000 : ℝ)*base70 + (187251689999031/369545000000000000000000000 : ℝ)*base72 + (75201641921911/324145000000000000000000000 : ℝ)*base75 + (27286093930367/369545000000000000000000000 : ℝ)*base77 + (23751242984258133111/47914465610000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (26347/100000000000000000 : ℝ)*base87 + (26347/100000000000000000 : ℝ)*base89 + (26347/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((73909/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73909/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64829/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-64829/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83759/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(83759/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((17103/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17103/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17553/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-17553/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(771/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(771/2500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312047_s1 p hpa hpb X hX hprev0

#print axioms solution

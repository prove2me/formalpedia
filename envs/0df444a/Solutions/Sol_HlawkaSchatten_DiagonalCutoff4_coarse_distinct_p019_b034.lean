-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p019_b034
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:28:35.00599+00:00
-- url     : https://prove2.me/submissions/39e5323d-bd8b-4d10-b342-d49b3633c58c

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
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
theorem collision_support_c319068_s0_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (58668011/78125000 : ℝ)*x 0 + (2646427373/10000000000 : ℝ)*x 1 + (-1724481109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58668011/78125000 : ℝ)^5 ≤ (13981190836051/20000000000000 : ℝ)^4 := by
    have hnat : (58668011 : ℕ)^5*20000000000000^4 ≤ 13981190836051^4*78125000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58668011 78125000 13981190836051 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2646427373/10000000000 : ℝ)^5 ≤ (18981257241969/100000000000000 : ℝ)^4 := by
    have hnat : (2646427373 : ℕ)^5*100000000000000^4 ≤ 18981257241969^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646427373 10000000000 18981257241969 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1724481109/10000000000 : ℝ)^5 ≤ (2778197141827/25000000000000 : ℝ)^4 := by
    have hnat : (1724481109 : ℕ)^5*25000000000000^4 ≤ 2778197141827^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724481109 10000000000 2778197141827 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(58668011/78125000 : ℝ), (2646427373/10000000000 : ℝ), (-1724481109/10000000000 : ℝ)] ![(13981190836051/20000000000000 : ℝ), (18981257241969/100000000000000 : ℝ), (2778197141827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(58668011/78125000 : ℝ)|^5 ≤ (13981190836051/20000000000000 : ℝ)^4
        have hw : |(58668011/78125000 : ℝ)|=(58668011/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2646427373/10000000000 : ℝ)|^5 ≤ (18981257241969/100000000000000 : ℝ)^4
        have hw : |(2646427373/10000000000 : ℝ)|=(2646427373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1724481109/10000000000 : ℝ)|^5 ≤ (2778197141827/25000000000000 : ℝ)^4
        have hw : |(-1724481109/10000000000 : ℝ)|=(1724481109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s0_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1989801567/5000000000 : ℝ)*x 0 + (-276499457/625000000 : ℝ)*x 1 + (4050305709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989801567/5000000000 : ℝ)^5 ≤ (31608195676183/100000000000000 : ℝ)^4 := by
    have hnat : (1989801567 : ℕ)^5*100000000000000^4 ≤ 31608195676183^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989801567 5000000000 31608195676183 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276499457/625000000 : ℝ)^5 ≤ (36080108241307/100000000000000 : ℝ)^4 := by
    have hnat : (276499457 : ℕ)^5*100000000000000^4 ≤ 36080108241307^4*625000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276499457 625000000 36080108241307 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4050305709/10000000000 : ℝ)^5 ≤ (1615584803659/5000000000000 : ℝ)^4 := by
    have hnat : (4050305709 : ℕ)^5*5000000000000^4 ≤ 1615584803659^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4050305709 10000000000 1615584803659 5000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1989801567/5000000000 : ℝ), (-276499457/625000000 : ℝ), (4050305709/10000000000 : ℝ)] ![(31608195676183/100000000000000 : ℝ), (36080108241307/100000000000000 : ℝ), (1615584803659/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1989801567/5000000000 : ℝ)|^5 ≤ (31608195676183/100000000000000 : ℝ)^4
        have hw : |(1989801567/5000000000 : ℝ)|=(1989801567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-276499457/625000000 : ℝ)|^5 ≤ (36080108241307/100000000000000 : ℝ)^4
        have hw : |(-276499457/625000000 : ℝ)|=(276499457/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4050305709/10000000000 : ℝ)|^5 ≤ (1615584803659/5000000000000 : ℝ)^4
        have hw : |(4050305709/10000000000 : ℝ)|=(4050305709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s0_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3417299469/10000000000 : ℝ)*x 0 + (-3677044343/10000000000 : ℝ)*x 1 + (-2650806871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3417299469/10000000000 : ℝ)^5 ≤ (1306392875273/5000000000000 : ℝ)^4 := by
    have hnat : (3417299469 : ℕ)^5*5000000000000^4 ≤ 1306392875273^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3417299469 10000000000 1306392875273 5000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3677044343/10000000000 : ℝ)^5 ≤ (7158360940793/25000000000000 : ℝ)^4 := by
    have hnat : (3677044343 : ℕ)^5*25000000000000^4 ≤ 7158360940793^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3677044343 10000000000 7158360940793 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2650806871/5000000000 : ℝ)^5 ≤ (9047739745197/20000000000000 : ℝ)^4 := by
    have hnat : (2650806871 : ℕ)^5*20000000000000^4 ≤ 9047739745197^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650806871 5000000000 9047739745197 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3417299469/10000000000 : ℝ), (-3677044343/10000000000 : ℝ), (-2650806871/5000000000 : ℝ)] ![(1306392875273/5000000000000 : ℝ), (7158360940793/25000000000000 : ℝ), (9047739745197/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3417299469/10000000000 : ℝ)|^5 ≤ (1306392875273/5000000000000 : ℝ)^4
        have hw : |(3417299469/10000000000 : ℝ)|=(3417299469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3677044343/10000000000 : ℝ)|^5 ≤ (7158360940793/25000000000000 : ℝ)^4
        have hw : |(-3677044343/10000000000 : ℝ)|=(3677044343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2650806871/5000000000 : ℝ)|^5 ≤ (9047739745197/20000000000000 : ℝ)^4
        have hw : |(-2650806871/5000000000 : ℝ)|=(2650806871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s0_7 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-540680269/10000000000 : ℝ)*x 0 + (-1373105763/2500000000 : ℝ)*x 1 + (-5753579479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540680269/10000000000 : ℝ)^5 ≤ (651801957129/25000000000000 : ℝ)^4 := by
    have hnat : (540680269 : ℕ)^5*25000000000000^4 ≤ 651801957129^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540680269 10000000000 651801957129 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1373105763/2500000000 : ℝ)^5 ≤ (47282994860113/100000000000000 : ℝ)^4 := by
    have hnat : (1373105763 : ℕ)^5*100000000000000^4 ≤ 47282994860113^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373105763 2500000000 47282994860113 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5753579479/10000000000 : ℝ)^5 ≤ (10021959458979/20000000000000 : ℝ)^4 := by
    have hnat : (5753579479 : ℕ)^5*20000000000000^4 ≤ 10021959458979^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5753579479 10000000000 10021959458979 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-540680269/10000000000 : ℝ), (-1373105763/2500000000 : ℝ), (-5753579479/10000000000 : ℝ)] ![(651801957129/25000000000000 : ℝ), (47282994860113/100000000000000 : ℝ), (10021959458979/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-540680269/10000000000 : ℝ)|^5 ≤ (651801957129/25000000000000 : ℝ)^4
        have hw : |(-540680269/10000000000 : ℝ)|=(540680269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1373105763/2500000000 : ℝ)|^5 ≤ (47282994860113/100000000000000 : ℝ)^4
        have hw : |(-1373105763/2500000000 : ℝ)|=(1373105763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5753579479/10000000000 : ℝ)|^5 ≤ (10021959458979/20000000000000 : ℝ)^4
        have hw : |(-5753579479/10000000000 : ℝ)|=(5753579479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s0_8 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (7510546421/10000000000 : ℝ)*x 0 + (122941153/400000000 : ℝ)*x 1 + (-304557207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7510546421/10000000000 : ℝ)^5 ≤ (69918067872187/100000000000000 : ℝ)^4 := by
    have hnat : (7510546421 : ℕ)^5*100000000000000^4 ≤ 69918067872187^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7510546421 10000000000 69918067872187 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122941153/400000000 : ℝ)^5 ≤ (915390928879/4000000000000 : ℝ)^4 := by
    have hnat : (122941153 : ℕ)^5*4000000000000^4 ≤ 915390928879^4*400000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122941153 400000000 915390928879 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (304557207/2500000000 : ℝ)^5 ≤ (899644860947/12500000000000 : ℝ)^4 := by
    have hnat : (304557207 : ℕ)^5*12500000000000^4 ≤ 899644860947^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304557207 2500000000 899644860947 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7510546421/10000000000 : ℝ), (122941153/400000000 : ℝ), (-304557207/2500000000 : ℝ)] ![(69918067872187/100000000000000 : ℝ), (915390928879/4000000000000 : ℝ), (899644860947/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7510546421/10000000000 : ℝ)|^5 ≤ (69918067872187/100000000000000 : ℝ)^4
        have hw : |(7510546421/10000000000 : ℝ)|=(7510546421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(122941153/400000000 : ℝ)|^5 ≤ (915390928879/4000000000000 : ℝ)^4
        have hw : |(122941153/400000000 : ℝ)|=(122941153/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-304557207/2500000000 : ℝ)|^5 ≤ (899644860947/12500000000000 : ℝ)^4
        have hw : |(-304557207/2500000000 : ℝ)|=(304557207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s0_9 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2352388203/5000000000 : ℝ)*x 0 + (-3102359323/10000000000 : ℝ)*x 1 + (4599845649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2352388203/5000000000 : ℝ)^5 ≤ (19482457606921/50000000000000 : ℝ)^4 := by
    have hnat : (2352388203 : ℕ)^5*50000000000000^4 ≤ 19482457606921^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2352388203 5000000000 19482457606921 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3102359323/10000000000 : ℝ)^5 ≤ (289417731301/1250000000000 : ℝ)^4 := by
    have hnat : (3102359323 : ℕ)^5*1250000000000^4 ≤ 289417731301^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3102359323 10000000000 289417731301 1250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4599845649/10000000000 : ℝ)^5 ≤ (18940833129949/50000000000000 : ℝ)^4 := by
    have hnat : (4599845649 : ℕ)^5*50000000000000^4 ≤ 18940833129949^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4599845649 10000000000 18940833129949 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2352388203/5000000000 : ℝ), (-3102359323/10000000000 : ℝ), (4599845649/10000000000 : ℝ)] ![(19482457606921/50000000000000 : ℝ), (289417731301/1250000000000 : ℝ), (18940833129949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2352388203/5000000000 : ℝ)|^5 ≤ (19482457606921/50000000000000 : ℝ)^4
        have hw : |(2352388203/5000000000 : ℝ)|=(2352388203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3102359323/10000000000 : ℝ)|^5 ≤ (289417731301/1250000000000 : ℝ)^4
        have hw : |(-3102359323/10000000000 : ℝ)|=(3102359323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4599845649/10000000000 : ℝ)|^5 ≤ (18940833129949/50000000000000 : ℝ)^4
        have hw : |(4599845649/10000000000 : ℝ)|=(4599845649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s0_13 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3529990601/10000000000 : ℝ)*x 0 + (-2470804721/10000000000 : ℝ)*x 1 + (-6231953613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3529990601/10000000000 : ℝ)^5 ≤ (850289777717/3125000000000 : ℝ)^4 := by
    have hnat : (3529990601 : ℕ)^5*3125000000000^4 ≤ 850289777717^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3529990601 10000000000 850289777717 3125000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2470804721/10000000000 : ℝ)^5 ≤ (3483999016693/20000000000000 : ℝ)^4 := by
    have hnat : (2470804721 : ℕ)^5*20000000000000^4 ≤ 3483999016693^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2470804721 10000000000 3483999016693 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6231953613/10000000000 : ℝ)^5 ≤ (27685366008931/50000000000000 : ℝ)^4 := by
    have hnat : (6231953613 : ℕ)^5*50000000000000^4 ≤ 27685366008931^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6231953613 10000000000 27685366008931 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3529990601/10000000000 : ℝ), (-2470804721/10000000000 : ℝ), (-6231953613/10000000000 : ℝ)] ![(850289777717/3125000000000 : ℝ), (3483999016693/20000000000000 : ℝ), (27685366008931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3529990601/10000000000 : ℝ)|^5 ≤ (850289777717/3125000000000 : ℝ)^4
        have hw : |(3529990601/10000000000 : ℝ)|=(3529990601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2470804721/10000000000 : ℝ)|^5 ≤ (3483999016693/20000000000000 : ℝ)^4
        have hw : |(-2470804721/10000000000 : ℝ)|=(2470804721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6231953613/10000000000 : ℝ)|^5 ≤ (27685366008931/50000000000000 : ℝ)^4
        have hw : |(-6231953613/10000000000 : ℝ)|=(6231953613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s0_14 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-279544897/10000000000 : ℝ)*x 0 + (-2253115723/5000000000 : ℝ)*x 1 + (-6816436537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279544897/10000000000 : ℝ)^5 ≤ (571523990597/50000000000000 : ℝ)^4 := by
    have hnat : (279544897 : ℕ)^5*50000000000000^4 ≤ 571523990597^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279544897 10000000000 571523990597 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253115723/5000000000 : ℝ)^5 ≤ (36920439938519/100000000000000 : ℝ)^4 := by
    have hnat : (2253115723 : ℕ)^5*100000000000000^4 ≤ 36920439938519^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253115723 5000000000 36920439938519 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6816436537/10000000000 : ℝ)^5 ≤ (6193651206773/10000000000000 : ℝ)^4 := by
    have hnat : (6816436537 : ℕ)^5*10000000000000^4 ≤ 6193651206773^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6816436537 10000000000 6193651206773 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-279544897/10000000000 : ℝ), (-2253115723/5000000000 : ℝ), (-6816436537/10000000000 : ℝ)] ![(571523990597/50000000000000 : ℝ), (36920439938519/100000000000000 : ℝ), (6193651206773/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-279544897/10000000000 : ℝ)|^5 ≤ (571523990597/50000000000000 : ℝ)^4
        have hw : |(-279544897/10000000000 : ℝ)|=(279544897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2253115723/5000000000 : ℝ)|^5 ≤ (36920439938519/100000000000000 : ℝ)^4
        have hw : |(-2253115723/5000000000 : ℝ)|=(2253115723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6816436537/10000000000 : ℝ)|^5 ≤ (6193651206773/10000000000000 : ℝ)^4
        have hw : |(-6816436537/10000000000 : ℝ)|=(6816436537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s0_15 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (65797141/78125000 : ℝ)*x 0 + (2234793481/10000000000 : ℝ)*x 1 + (-754372343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65797141/78125000 : ℝ)^5 ≤ (80680994165697/100000000000000 : ℝ)^4 := by
    have hnat : (65797141 : ℕ)^5*100000000000000^4 ≤ 80680994165697^4*78125000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65797141 78125000 80680994165697 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2234793481/10000000000 : ℝ)^5 ≤ (614620067701/4000000000000 : ℝ)^4 := by
    have hnat : (2234793481 : ℕ)^5*4000000000000^4 ≤ 614620067701^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234793481 10000000000 614620067701 4000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (754372343/10000000000 : ℝ)^5 ≤ (3953504133959/100000000000000 : ℝ)^4 := by
    have hnat : (754372343 : ℕ)^5*100000000000000^4 ≤ 3953504133959^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754372343 10000000000 3953504133959 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65797141/78125000 : ℝ), (2234793481/10000000000 : ℝ), (-754372343/10000000000 : ℝ)] ![(80680994165697/100000000000000 : ℝ), (614620067701/4000000000000 : ℝ), (3953504133959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65797141/78125000 : ℝ)|^5 ≤ (80680994165697/100000000000000 : ℝ)^4
        have hw : |(65797141/78125000 : ℝ)|=(65797141/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2234793481/10000000000 : ℝ)|^5 ≤ (614620067701/4000000000000 : ℝ)^4
        have hw : |(2234793481/10000000000 : ℝ)|=(2234793481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-754372343/10000000000 : ℝ)|^5 ≤ (3953504133959/100000000000000 : ℝ)^4
        have hw : |(-754372343/10000000000 : ℝ)|=(754372343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s0_16 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (1076803209/2500000000 : ℝ)*x 0 + (-2264248839/5000000000 : ℝ)*x 1 + (3607468161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076803209/2500000000 : ℝ)^5 ≤ (34893570859667/100000000000000 : ℝ)^4 := by
    have hnat : (1076803209 : ℕ)^5*100000000000000^4 ≤ 34893570859667^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076803209 2500000000 34893570859667 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264248839/5000000000 : ℝ)^5 ≤ (9287155033197/25000000000000 : ℝ)^4 := by
    have hnat : (2264248839 : ℕ)^5*25000000000000^4 ≤ 9287155033197^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264248839 5000000000 9287155033197 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3607468161/10000000000 : ℝ)^5 ≤ (13978904495879/50000000000000 : ℝ)^4 := by
    have hnat : (3607468161 : ℕ)^5*50000000000000^4 ≤ 13978904495879^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3607468161 10000000000 13978904495879 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076803209/2500000000 : ℝ), (-2264248839/5000000000 : ℝ), (3607468161/10000000000 : ℝ)] ![(34893570859667/100000000000000 : ℝ), (9287155033197/25000000000000 : ℝ), (13978904495879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076803209/2500000000 : ℝ)|^5 ≤ (34893570859667/100000000000000 : ℝ)^4
        have hw : |(1076803209/2500000000 : ℝ)|=(1076803209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2264248839/5000000000 : ℝ)|^5 ≤ (9287155033197/25000000000000 : ℝ)^4
        have hw : |(-2264248839/5000000000 : ℝ)|=(2264248839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3607468161/10000000000 : ℝ)|^5 ≤ (13978904495879/50000000000000 : ℝ)^4
        have hw : |(3607468161/10000000000 : ℝ)|=(3607468161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s0_20 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2613900057/10000000000 : ℝ)*x 0 + (-538015473/2000000000 : ℝ)*x 1 + (-6816436537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613900057/10000000000 : ℝ)^5 ≤ (9345041344149/50000000000000 : ℝ)^4 := by
    have hnat : (2613900057 : ℕ)^5*50000000000000^4 ≤ 9345041344149^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613900057 10000000000 9345041344149 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538015473/2000000000 : ℝ)^5 ≤ (4843351309353/25000000000000 : ℝ)^4 := by
    have hnat : (538015473 : ℕ)^5*25000000000000^4 ≤ 4843351309353^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538015473 2000000000 4843351309353 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6816436537/10000000000 : ℝ)^5 ≤ (6193651206773/10000000000000 : ℝ)^4 := by
    have hnat : (6816436537 : ℕ)^5*10000000000000^4 ≤ 6193651206773^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6816436537 10000000000 6193651206773 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613900057/10000000000 : ℝ), (-538015473/2000000000 : ℝ), (-6816436537/10000000000 : ℝ)] ![(9345041344149/50000000000000 : ℝ), (4843351309353/25000000000000 : ℝ), (6193651206773/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613900057/10000000000 : ℝ)|^5 ≤ (9345041344149/50000000000000 : ℝ)^4
        have hw : |(2613900057/10000000000 : ℝ)|=(2613900057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-538015473/2000000000 : ℝ)|^5 ≤ (4843351309353/25000000000000 : ℝ)^4
        have hw : |(-538015473/2000000000 : ℝ)|=(538015473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6816436537/10000000000 : ℝ)|^5 ≤ (6193651206773/10000000000000 : ℝ)^4
        have hw : |(-6816436537/10000000000 : ℝ)|=(6816436537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s0_21 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-890617/39062500 : ℝ)*x 0 + (-1518010507/2500000000 : ℝ)*x 1 + (-1331842489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (890617/39062500 : ℝ)^5 ≤ (44297955933/5000000000000 : ℝ)^4 := by
    have hnat : (890617 : ℕ)^5*5000000000000^4 ≤ 44297955933^4*39062500^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890617 39062500 44297955933 5000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1518010507/2500000000 : ℝ)^5 ≤ (10720090624741/20000000000000 : ℝ)^4 := by
    have hnat : (1518010507 : ℕ)^5*20000000000000^4 ≤ 10720090624741^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518010507 2500000000 10720090624741 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1331842489/2500000000 : ℝ)^5 ≤ (4551358774693/10000000000000 : ℝ)^4 := by
    have hnat : (1331842489 : ℕ)^5*10000000000000^4 ≤ 4551358774693^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331842489 2500000000 4551358774693 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-890617/39062500 : ℝ), (-1518010507/2500000000 : ℝ), (-1331842489/2500000000 : ℝ)] ![(44297955933/5000000000000 : ℝ), (10720090624741/20000000000000 : ℝ), (4551358774693/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-890617/39062500 : ℝ)|^5 ≤ (44297955933/5000000000000 : ℝ)^4
        have hw : |(-890617/39062500 : ℝ)|=(890617/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1518010507/2500000000 : ℝ)|^5 ≤ (10720090624741/20000000000000 : ℝ)^4
        have hw : |(-1518010507/2500000000 : ℝ)|=(1518010507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1331842489/2500000000 : ℝ)|^5 ≤ (4551358774693/10000000000000 : ℝ)^4
        have hw : |(-1331842489/2500000000 : ℝ)|=(1331842489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s0_22 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (2179661213/2500000000 : ℝ)*x 0 + (1805308347/10000000000 : ℝ)*x 1 + (-759031027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179661213/2500000000 : ℝ)^5 ≤ (84248317057103/100000000000000 : ℝ)^4 := by
    have hnat : (2179661213 : ℕ)^5*100000000000000^4 ≤ 84248317057103^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179661213 2500000000 84248317057103 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1805308347/10000000000 : ℝ)^5 ≤ (11767636311391/100000000000000 : ℝ)^4 := by
    have hnat : (1805308347 : ℕ)^5*100000000000000^4 ≤ 11767636311391^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1805308347 10000000000 11767636311391 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (759031027/10000000000 : ℝ)^5 ≤ (996011653747/25000000000000 : ℝ)^4 := by
    have hnat : (759031027 : ℕ)^5*25000000000000^4 ≤ 996011653747^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759031027 10000000000 996011653747 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179661213/2500000000 : ℝ), (1805308347/10000000000 : ℝ), (-759031027/10000000000 : ℝ)] ![(84248317057103/100000000000000 : ℝ), (11767636311391/100000000000000 : ℝ), (996011653747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179661213/2500000000 : ℝ)|^5 ≤ (84248317057103/100000000000000 : ℝ)^4
        have hw : |(2179661213/2500000000 : ℝ)|=(2179661213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1805308347/10000000000 : ℝ)|^5 ≤ (11767636311391/100000000000000 : ℝ)^4
        have hw : |(1805308347/10000000000 : ℝ)|=(1805308347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-759031027/10000000000 : ℝ)|^5 ≤ (996011653747/25000000000000 : ℝ)^4
        have hw : |(-759031027/10000000000 : ℝ)|=(759031027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s0_23 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (440979331/1250000000 : ℝ)*x 0 + (-4436701593/10000000000 : ℝ)*x 1 + (4475088851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440979331/1250000000 : ℝ)^5 ≤ (1699281361593/6250000000000 : ℝ)^4 := by
    have hnat : (440979331 : ℕ)^5*6250000000000^4 ≤ 1699281361593^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440979331 1250000000 1699281361593 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4436701593/10000000000 : ℝ)^5 ≤ (36209729000109/100000000000000 : ℝ)^4 := by
    have hnat : (4436701593 : ℕ)^5*100000000000000^4 ≤ 36209729000109^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4436701593 10000000000 36209729000109 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4475088851/10000000000 : ℝ)^5 ≤ (18300884596997/50000000000000 : ℝ)^4 := by
    have hnat : (4475088851 : ℕ)^5*50000000000000^4 ≤ 18300884596997^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475088851 10000000000 18300884596997 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(440979331/1250000000 : ℝ), (-4436701593/10000000000 : ℝ), (4475088851/10000000000 : ℝ)] ![(1699281361593/6250000000000 : ℝ), (36209729000109/100000000000000 : ℝ), (18300884596997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(440979331/1250000000 : ℝ)|^5 ≤ (1699281361593/6250000000000 : ℝ)^4
        have hw : |(440979331/1250000000 : ℝ)|=(440979331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4436701593/10000000000 : ℝ)|^5 ≤ (36209729000109/100000000000000 : ℝ)^4
        have hw : |(-4436701593/10000000000 : ℝ)|=(4436701593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4475088851/10000000000 : ℝ)|^5 ≤ (18300884596997/50000000000000 : ℝ)^4
        have hw : |(4475088851/10000000000 : ℝ)|=(4475088851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s0_27 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (664421751/2000000000 : ℝ)*x 0 + (-3654099/9765625 : ℝ)*x 1 + (-1331842489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664421751/2000000000 : ℝ)^5 ≤ (25221290661191/100000000000000 : ℝ)^4 := by
    have hnat : (664421751 : ℕ)^5*100000000000000^4 ≤ 25221290661191^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664421751 2000000000 25221290661191 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3654099/9765625 : ℝ)^5 ≤ (29265121574527/100000000000000 : ℝ)^4 := by
    have hnat : (3654099 : ℕ)^5*100000000000000^4 ≤ 29265121574527^4*9765625^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3654099 9765625 29265121574527 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1331842489/2500000000 : ℝ)^5 ≤ (4551358774693/10000000000000 : ℝ)^4 := by
    have hnat : (1331842489 : ℕ)^5*10000000000000^4 ≤ 4551358774693^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331842489 2500000000 4551358774693 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664421751/2000000000 : ℝ), (-3654099/9765625 : ℝ), (-1331842489/2500000000 : ℝ)] ![(25221290661191/100000000000000 : ℝ), (29265121574527/100000000000000 : ℝ), (4551358774693/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664421751/2000000000 : ℝ)|^5 ≤ (25221290661191/100000000000000 : ℝ)^4
        have hw : |(664421751/2000000000 : ℝ)|=(664421751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3654099/9765625 : ℝ)|^5 ≤ (29265121574527/100000000000000 : ℝ)^4
        have hw : |(-3654099/9765625 : ℝ)|=(3654099/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1331842489/2500000000 : ℝ)|^5 ≤ (4551358774693/10000000000000 : ℝ)^4
        have hw : |(-1331842489/2500000000 : ℝ)|=(1331842489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s1_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-2198086873/10000000000 : ℝ)*x 0 + (-37360263/78125000 : ℝ)*x 1 + (-5296310049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2198086873/10000000000 : ℝ)^5 ≤ (3762669512433/25000000000000 : ℝ)^4 := by
    have hnat : (2198086873 : ℕ)^5*25000000000000^4 ≤ 3762669512433^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198086873 10000000000 3762669512433 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37360263/78125000 : ℝ)^5 ≤ (3976718668563/10000000000000 : ℝ)^4 := by
    have hnat : (37360263 : ℕ)^5*10000000000000^4 ≤ 3976718668563^4*78125000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37360263 78125000 3976718668563 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5296310049/10000000000 : ℝ)^5 ≤ (2259106762527/5000000000000 : ℝ)^4 := by
    have hnat : (5296310049 : ℕ)^5*5000000000000^4 ≤ 2259106762527^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296310049 10000000000 2259106762527 5000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2198086873/10000000000 : ℝ), (-37360263/78125000 : ℝ), (-5296310049/10000000000 : ℝ)] ![(3762669512433/25000000000000 : ℝ), (3976718668563/10000000000000 : ℝ), (2259106762527/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2198086873/10000000000 : ℝ)|^5 ≤ (3762669512433/25000000000000 : ℝ)^4
        have hw : |(-2198086873/10000000000 : ℝ)|=(2198086873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37360263/78125000 : ℝ)|^5 ≤ (3976718668563/10000000000000 : ℝ)^4
        have hw : |(-37360263/78125000 : ℝ)|=(37360263/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5296310049/10000000000 : ℝ)|^5 ≤ (2259106762527/5000000000000 : ℝ)^4
        have hw : |(-5296310049/10000000000 : ℝ)|=(5296310049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s1_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (3077058789/5000000000 : ℝ)*x 0 + (3201141751/10000000000 : ℝ)*x 1 + (-2914437349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3077058789/5000000000 : ℝ)^5 ≤ (27253811081073/50000000000000 : ℝ)^4 := by
    have hnat : (3077058789 : ℕ)^5*50000000000000^4 ≤ 27253811081073^4*5000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3077058789 5000000000 27253811081073 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3201141751/10000000000 : ℝ)^5 ≤ (24078594455307/100000000000000 : ℝ)^4 := by
    have hnat : (3201141751 : ℕ)^5*100000000000000^4 ≤ 24078594455307^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3201141751 10000000000 24078594455307 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2914437349/10000000000 : ℝ)^5 ≤ (267672292069/1250000000000 : ℝ)^4 := by
    have hnat : (2914437349 : ℕ)^5*1250000000000^4 ≤ 267672292069^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2914437349 10000000000 267672292069 1250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3077058789/5000000000 : ℝ), (3201141751/10000000000 : ℝ), (-2914437349/10000000000 : ℝ)] ![(27253811081073/50000000000000 : ℝ), (24078594455307/100000000000000 : ℝ), (267672292069/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3077058789/5000000000 : ℝ)|^5 ≤ (27253811081073/50000000000000 : ℝ)^4
        have hw : |(3077058789/5000000000 : ℝ)|=(3077058789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3201141751/10000000000 : ℝ)|^5 ≤ (24078594455307/100000000000000 : ℝ)^4
        have hw : |(3201141751/10000000000 : ℝ)|=(3201141751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2914437349/10000000000 : ℝ)|^5 ≤ (267672292069/1250000000000 : ℝ)^4
        have hw : |(-2914437349/10000000000 : ℝ)|=(2914437349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s1_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (511526377/1250000000 : ℝ)*x 0 + (-4377342677/10000000000 : ℝ)*x 1 + (3985293991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511526377/1250000000 : ℝ)^5 ≤ (204563215889/625000000000 : ℝ)^4 := by
    have hnat : (511526377 : ℕ)^5*625000000000^4 ≤ 204563215889^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511526377 1250000000 204563215889 625000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4377342677/10000000000 : ℝ)^5 ≤ (7121035955577/20000000000000 : ℝ)^4 := by
    have hnat : (4377342677 : ℕ)^5*20000000000000^4 ≤ 7121035955577^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377342677 10000000000 7121035955577 20000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3985293991/10000000000 : ℝ)^5 ≤ (1979044104073/6250000000000 : ℝ)^4 := by
    have hnat : (3985293991 : ℕ)^5*6250000000000^4 ≤ 1979044104073^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3985293991 10000000000 1979044104073 6250000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(511526377/1250000000 : ℝ), (-4377342677/10000000000 : ℝ), (3985293991/10000000000 : ℝ)] ![(204563215889/625000000000 : ℝ), (7121035955577/20000000000000 : ℝ), (1979044104073/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(511526377/1250000000 : ℝ)|^5 ≤ (204563215889/625000000000 : ℝ)^4
        have hw : |(511526377/1250000000 : ℝ)|=(511526377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4377342677/10000000000 : ℝ)|^5 ≤ (7121035955577/20000000000000 : ℝ)^4
        have hw : |(-4377342677/10000000000 : ℝ)|=(4377342677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3985293991/10000000000 : ℝ)|^5 ≤ (1979044104073/6250000000000 : ℝ)^4
        have hw : |(3985293991/10000000000 : ℝ)|=(3985293991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319068_s1_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (963770333/2500000000 : ℝ)*x 0 + (-1019612581/2500000000 : ℝ)*x 1 + (-903397073/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (963770333/2500000000 : ℝ)^5 ≤ (7594198415213/25000000000000 : ℝ)^4 := by
    have hnat : (963770333 : ℕ)^5*25000000000000^4 ≤ 7594198415213^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963770333 2500000000 7594198415213 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1019612581/2500000000 : ℝ)^5 ≤ (32592597332301/100000000000000 : ℝ)^4 := by
    have hnat : (1019612581 : ℕ)^5*100000000000000^4 ≤ 32592597332301^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019612581 2500000000 32592597332301 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903397073/2000000000 : ℝ)^5 ≤ (37030608988397/100000000000000 : ℝ)^4 := by
    have hnat : (903397073 : ℕ)^5*100000000000000^4 ≤ 37030608988397^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903397073 2000000000 37030608988397 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(963770333/2500000000 : ℝ), (-1019612581/2500000000 : ℝ), (-903397073/2000000000 : ℝ)] ![(7594198415213/25000000000000 : ℝ), (32592597332301/100000000000000 : ℝ), (37030608988397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(963770333/2500000000 : ℝ)|^5 ≤ (7594198415213/25000000000000 : ℝ)^4
        have hw : |(963770333/2500000000 : ℝ)|=(963770333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1019612581/2500000000 : ℝ)|^5 ≤ (32592597332301/100000000000000 : ℝ)^4
        have hw : |(-1019612581/2500000000 : ℝ)|=(1019612581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-903397073/2000000000 : ℝ)|^5 ≤ (37030608988397/100000000000000 : ℝ)^4
        have hw : |(-903397073/2000000000 : ℝ)|=(903397073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319068 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((58668011/78125000 : ℝ)*X 1 0+(2646427373/10000000000 : ℝ)*X 1 1+(-1724481109/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1989801567/5000000000 : ℝ)*X 2 0+(-276499457/625000000 : ℝ)*X 2 1+(4050305709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((3417299469/10000000000 : ℝ)*X 0 0+(-3677044343/10000000000 : ℝ)*X 0 1+(-2650806871/5000000000 : ℝ)*X 0 2+(3417299469/10000000000 : ℝ)*X 1 0+(-3677044343/10000000000 : ℝ)*X 1 1+(-2650806871/5000000000 : ℝ)*X 1 2+(3417299469/10000000000 : ℝ)*X 2 0+(-3677044343/10000000000 : ℝ)*X 2 1+(-2650806871/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-540680269/10000000000 : ℝ)*X 0 0+(-1373105763/2500000000 : ℝ)*X 0 1+(-5753579479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((7510546421/10000000000 : ℝ)*X 1 0+(122941153/400000000 : ℝ)*X 1 1+(-304557207/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2352388203/5000000000 : ℝ)*X 2 0+(-3102359323/10000000000 : ℝ)*X 2 1+(4599845649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3529990601/10000000000 : ℝ)*X 0 0+(-2470804721/10000000000 : ℝ)*X 0 1+(-6231953613/10000000000 : ℝ)*X 0 2+(3529990601/10000000000 : ℝ)*X 1 0+(-2470804721/10000000000 : ℝ)*X 1 1+(-6231953613/10000000000 : ℝ)*X 1 2+(3529990601/10000000000 : ℝ)*X 2 0+(-2470804721/10000000000 : ℝ)*X 2 1+(-6231953613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-279544897/10000000000 : ℝ)*X 0 0+(-2253115723/5000000000 : ℝ)*X 0 1+(-6816436537/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((65797141/78125000 : ℝ)*X 1 0+(2234793481/10000000000 : ℝ)*X 1 1+(-754372343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1076803209/2500000000 : ℝ)*X 2 0+(-2264248839/5000000000 : ℝ)*X 2 1+(3607468161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2613900057/10000000000 : ℝ)*X 0 0+(-538015473/2000000000 : ℝ)*X 0 1+(-6816436537/10000000000 : ℝ)*X 0 2+(2613900057/10000000000 : ℝ)*X 1 0+(-538015473/2000000000 : ℝ)*X 1 1+(-6816436537/10000000000 : ℝ)*X 1 2+(2613900057/10000000000 : ℝ)*X 2 0+(-538015473/2000000000 : ℝ)*X 2 1+(-6816436537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-890617/39062500 : ℝ)*X 0 0+(-1518010507/2500000000 : ℝ)*X 0 1+(-1331842489/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2179661213/2500000000 : ℝ)*X 1 0+(1805308347/10000000000 : ℝ)*X 1 1+(-759031027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((440979331/1250000000 : ℝ)*X 2 0+(-4436701593/10000000000 : ℝ)*X 2 1+(4475088851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((664421751/2000000000 : ℝ)*X 0 0+(-3654099/9765625 : ℝ)*X 0 1+(-1331842489/2500000000 : ℝ)*X 0 2+(664421751/2000000000 : ℝ)*X 1 0+(-3654099/9765625 : ℝ)*X 1 1+(-1331842489/2500000000 : ℝ)*X 1 2+(664421751/2000000000 : ℝ)*X 2 0+(-3654099/9765625 : ℝ)*X 2 1+(-1331842489/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((13717/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13717/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4904344397772512747709/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1362860009623/1000000000000 : ℝ)*(base1) + (912774887187/500000000000 : ℝ)*(base39) + (404539492617/1000000000000 : ℝ)*(base49) + (1785951/1000000000000 : ℝ)*(base60) + (2522572106211/1000000000000 : ℝ)*(major_s0_0) + (2522572106211/1000000000000 : ℝ)*(major_s0_1) + (2522572106211/1000000000000 : ℝ)*(major_s0_2) + (14724499/500000000000 : ℝ)*(sp_s0_1) + (2522567241957/500000000000 : ℝ)*(sp_s0_7) + (3682251875283/1000000000000 : ℝ)*(sp_s0_8) + (3682251793563/1000000000000 : ℝ)*(sp_s0_9) + (4046861/500000000000 : ℝ)*(sp_s0_14) + (310933/250000000000 : ℝ)*(sp_s0_15) + (615489/20000000000 : ℝ)*(sp_s0_23) + (1362860009623/1000000000000 : ℝ)*(f.failure) + (3682282568013/1000000000000 : ℝ)*(f.sum) + (3302337937443701/5000000000000000000000000000 : ℝ)*base63 + (9623719693533083/10000000000000000000000000000 : ℝ)*base65 + (6738327298645681/10000000000000000000000000000 : ℝ)*base67 + (1796986241645681/10000000000000000000000000000 : ℝ)*base68 + (1469140276943701/5000000000000000000000000000 : ℝ)*base71 + (1091210971533083/10000000000000000000000000000 : ℝ)*base72 + (1712866024466917/10000000000000000000000000000 : ℝ)*base74 + (3451930920354319/10000000000000000000000000000 : ℝ)*base77 + (2713280355943701/5000000000000000000000000000 : ℝ)*base78 + (29781/50000000000000000 : ℝ)*base87 + (29781/50000000000000000 : ℝ)*base89 + (29781/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-10489/25000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-10489/25000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10400239496826332906361/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (809267859609/1000000000000 : ℝ)*(base1) + (2542162345029/1000000000000 : ℝ)*(base39) + (830416128723/1000000000000 : ℝ)*(base49) + (822929250669/1000000000000 : ℝ)*(base60) + (2352159300157/500000000000 : ℝ)*(major_s0_0) + (2352159300157/500000000000 : ℝ)*(major_s0_1) + (2352159300157/500000000000 : ℝ)*(major_s0_2) + (4591157/125000000000 : ℝ)*(sp_s0_8) + (34013201/1000000000000 : ℝ)*(sp_s0_9) + (16295077/500000000000 : ℝ)*(sp_s0_13) + (383815938347/50000000000 : ℝ)*(sp_s0_14) + (3433507089037/500000000000 : ℝ)*(sp_s0_15) + (6867016894129/1000000000000 : ℝ)*(sp_s0_16) + (433070767533/250000000000 : ℝ)*(sp_s0_20) + (508316703979/200000000000 : ℝ)*(f.failure) + (686705090733/100000000000 : ℝ)*(f.sum) + (208646604156213/2500000000000000000000000000 : ℝ)*base62 + (3022348984567621/5000000000000000000000000000 : ℝ)*base65 + (4774400549880047/5000000000000000000000000000 : ℝ)*base67 + (2156585719880047/5000000000000000000000000000 : ℝ)*base68 + (251996975343787/2500000000000000000000000000 : ℝ)*base71 + (4375057560432379/5000000000000000000000000000 : ℝ)*base73 + (1202346006432379/5000000000000000000000000000 : ℝ)*base74 + (1829729782619953/5000000000000000000000000000 : ℝ)*base77 + (1732987896656213/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (4513/10000000000000000 : ℝ)*base87 + (4513/10000000000000000 : ℝ)*base89 + (4513/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-14629/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-14629/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (29750038100359384915503/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4695619987/1000000000000 : ℝ)*(base1) + (1436030753237/1000000000000 : ℝ)*(base39) + (17806609451/25000000000 : ℝ)*(base49) + (8283670197/250000000000 : ℝ)*(base60) + (3432326994369/1000000000000 : ℝ)*(major_s0_0) + (3432326994369/1000000000000 : ℝ)*(major_s0_1) + (3432326994369/1000000000000 : ℝ)*(major_s0_2) + (10541969/500000000000 : ℝ)*(sp_s0_2) + (14947959/40000000000 : ℝ)*(sp_s0_6) + (162474113/1000000000000 : ℝ)*(sp_s0_15) + (5014977956801/1000000000000 : ℝ)*(sp_s0_21) + (5010119862701/1000000000000 : ℝ)*(sp_s0_22) + (1252565313219/250000000000 : ℝ)*(sp_s0_23) + (924650174811/500000000000 : ℝ)*(sp_s0_27) + (231796208573/125000000000 : ℝ)*(f.failure) + (2505141168407/500000000000 : ℝ)*(f.sum) + (886181192560921/5000000000000000000000000000 : ℝ)*base62 + (6453204116760343/10000000000000000000000000000 : ℝ)*base64 + (2596785951638501/10000000000000000000000000000 : ℝ)*base66 + (985421771361499/10000000000000000000000000000 : ℝ)*base68 + (2293215677560921/5000000000000000000000000000 : ℝ)*base70 + (6705771390239657/10000000000000000000000000000 : ℝ)*base72 + (4590728933239657/10000000000000000000000000000 : ℝ)*base75 + (2569253789361499/10000000000000000000000000000 : ℝ)*base76 + (2227233691939079/5000000000000000000000000000 : ℝ)*base78 + (819/6250000000000000 : ℝ)*base86 + (819/6250000000000000 : ℝ)*base88 + (819/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (13717/100000 : ℝ) ^ (79/16 : ℝ) ≤ (5498155228180869/100000000000000000000 : ℝ) := by
    have hpowers : (13717/100000 : ℝ)^79 ≤ (5498155228180869/100000000000000000000 : ℝ)^16 := by
      have hnat : (13717 : ℕ)^79*100000000000000000000^16 ≤ 5498155228180869^16*100000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13717 100000 5498155228180869 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13717/100000 : ℝ)) (X := (5498155228180869/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100005498155228180869/100000000000000000000 : ℝ) ≤ (5000055676300719/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (100005498155228180869/100000000000000000000 : ℝ)^16 ≤ (5000055676300719/5000000000000000 : ℝ)^79 := by
      have hnat : (100005498155228180869 : ℕ)^16*5000000000000000^79 ≤ 5000055676300719^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100005498155228180869 100000000000000000000 5000055676300719 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000055676300719/5000000000000000 : ℝ)) (X := (100005498155228180869/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50005498155228180869/50000000000000000000 : ℝ) ≤ (10000222700320879/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (50005498155228180869/50000000000000000000 : ℝ)^16 ≤ (10000222700320879/10000000000000000 : ℝ)^79 := by
      have hnat : (50005498155228180869 : ℕ)^16*10000000000000000^79 ≤ 10000222700320879^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005498155228180869 50000000000000000000 10000222700320879 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000222700320879/10000000000000000 : ℝ)) (X := (50005498155228180869/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(55676300719/685850000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(111347719441/1371700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (13717/100000 : ℝ)) (alpha := (55676300719/685850000000000 : ℝ)) (beta := (111347719441/1371700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (13717/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(55676300719/685850000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(111347719441/1371700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (10489/25000 : ℝ) ^ (79/16 : ℝ) ≤ (1372605560475726583/100000000000000000000 : ℝ) := by
    have hpowers : (10489/25000 : ℝ)^79 ≤ (1372605560475726583/100000000000000000000 : ℝ)^16 := by
      have hnat : (10489 : ℕ)^79*100000000000000000000^16 ≤ 1372605560475726583^16*25000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10489 25000 1372605560475726583 100000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10489/25000 : ℝ)) (X := (1372605560475726583/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (101372605560475726583/100000000000000000000 : ℝ) ≤ (313364021784761/312500000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (101372605560475726583/100000000000000000000 : ℝ)^16 ≤ (313364021784761/312500000000000 : ℝ)^79 := by
      have hnat : (101372605560475726583 : ℕ)^16*312500000000000^79 ≤ 313364021784761^79*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101372605560475726583 100000000000000000000 313364021784761 312500000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (313364021784761/312500000000000 : ℝ)) (X := (101372605560475726583/100000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (51372605560475726583/50000000000000000000 : ℝ) ≤ (5027500220134051/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (51372605560475726583/50000000000000000000 : ℝ)^16 ≤ (5027500220134051/5000000000000000 : ℝ)^79 := by
      have hnat : (51372605560475726583 : ℕ)^16*5000000000000000^79 ≤ 5027500220134051^79*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51372605560475726583 50000000000000000000 5027500220134051 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027500220134051/5000000000000000 : ℝ)) (X := (51372605560475726583/50000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(864021784761/131112500000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(109406972623/16782400000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (10489/25000 : ℝ)) (alpha := (864021784761/131112500000000 : ℝ)) (beta := (109406972623/16782400000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (10489/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(864021784761/131112500000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(109406972623/16782400000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (14629/50000 : ℝ) ^ (79/16 : ℝ) ≤ (46303400205742227/20000000000000000000 : ℝ) := by
    have hpowers : (14629/50000 : ℝ)^79 ≤ (46303400205742227/20000000000000000000 : ℝ)^16 := by
      have hnat : (14629 : ℕ)^79*20000000000000000000^16 ≤ 46303400205742227^16*50000^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14629 50000 46303400205742227 20000000000000000000 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14629/50000 : ℝ)) (X := (46303400205742227/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (20046303400205742227/20000000000000000000 : ℝ) ≤ (5002342314683637/5000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (20046303400205742227/20000000000000000000 : ℝ)^16 ≤ (5002342314683637/5000000000000000 : ℝ)^79 := by
      have hnat : (20046303400205742227 : ℕ)^16*5000000000000000^79 ≤ 5002342314683637^79*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20046303400205742227 20000000000000000000 5002342314683637 5000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002342314683637/5000000000000000 : ℝ)) (X := (20046303400205742227/20000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (10046303400205742227/10000000000000000000 : ℝ) ≤ (2502340159382779/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (10046303400205742227/10000000000000000000 : ℝ)^16 ≤ (2502340159382779/2500000000000000 : ℝ)^79 := by
      have hnat : (10046303400205742227 : ℕ)^16*2500000000000000^79 ≤ 2502340159382779^79*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10046303400205742227 10000000000000000000 2502340159382779 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502340159382779/2500000000000000 : ℝ)) (X := (10046303400205742227/10000000000000000000 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(2342314683637/1462900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(2338004081921/1462900000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (14629/50000 : ℝ)) (alpha := (2342314683637/1462900000000000 : ℝ)) (beta := (2338004081921/1462900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (14629/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(2342314683637/1462900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(2338004081921/1462900000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2198086873/10000000000 : ℝ)*X 0 0+(-37360263/78125000 : ℝ)*X 0 1+(-5296310049/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3077058789/5000000000 : ℝ)*X 1 0+(3201141751/10000000000 : ℝ)*X 1 1+(-2914437349/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((511526377/1250000000 : ℝ)*X 2 0+(-4377342677/10000000000 : ℝ)*X 2 1+(3985293991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((963770333/2500000000 : ℝ)*X 0 0+(-1019612581/2500000000 : ℝ)*X 0 1+(-903397073/2000000000 : ℝ)*X 0 2+(963770333/2500000000 : ℝ)*X 1 0+(-1019612581/2500000000 : ℝ)*X 1 1+(-903397073/2000000000 : ℝ)*X 1 2+(963770333/2500000000 : ℝ)*X 2 0+(-1019612581/2500000000 : ℝ)*X 2 1+(-903397073/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319068_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-202641/25000 : ℝ) < ((-92547/50000 : ℝ)*P 0+(-92547/50000 : ℝ)*P 1+(-92547/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-202641/25000 : ℝ) < (-2453514883440787783090664825319/306887162000000000000000000000 : ℝ) := by norm_num
    linear_combination (3647/1000000000000 : ℝ)*(base3) + (8257/1000000000000 : ℝ)*(base21) + (56175909703/62500000000 : ℝ)*(base39) + (34550713211/125000000000 : ℝ)*(base40) + (181406201273/500000000000 : ℝ)*(base49) + (171644770297/1000000000000 : ℝ)*(base60) + (231367500291/125000000000 : ℝ)*(major_s1_0) + (92547/50000 : ℝ)*(major_s1_1) + (92547/50000 : ℝ)*(major_s1_2) + (166559242579/62500000000 : ℝ)*(sp_s1_0) + (2664947887239/1000000000000 : ℝ)*(sp_s1_1) + (333118484453/125000000000 : ℝ)*(sp_s1_2) + (999999996353/1000000000000 : ℝ)*(sp_s1_6) + (166559242579/62500000000 : ℝ)*(f.sum) + (130287598762301661/383608952500000000000000000000 : ℝ)*base62 + (22430947179207/36572500000000000000000000 : ℝ)*base64 + (15277816653091/104890000000000000000000000 : ℝ)*base66 + (8649944622801/73145000000000000000000000 : ℝ)*base68 + (1768604377560372577/10033299650000000000000000000000 : ℝ)*base70 + (48088586960521/171462500000000000000000000 : ℝ)*base73 + (3086031236399/5244500000000000000000000 : ℝ)*base75 + (1927727254633/171462500000000000000000000 : ℝ)*base77 + (2075803616592253052599/7193880650000000000000000000000 : ℝ)*base78 + (291/125000000000 : ℝ)*base83 + (2617/1000000000000 : ℝ)*base85 + (291/125000000000 : ℝ)*base86 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c319069_s0_0 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (-412002569/2000000000 : ℝ)*x 0 + (-880333063/1250000000 : ℝ)*x 1 + (2935249139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412002569/2000000000 : ℝ)^5 ≤ (13878336407379/100000000000000 : ℝ)^4 := by
    have hnat : (412002569 : ℕ)^5*100000000000000^4 ≤ 13878336407379^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412002569 2000000000 13878336407379 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (880333063/1250000000 : ℝ)^5 ≤ (32258283508683/50000000000000 : ℝ)^4 := by
    have hnat : (880333063 : ℕ)^5*50000000000000^4 ≤ 32258283508683^4*1250000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880333063 1250000000 32258283508683 50000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2935249139/10000000000 : ℝ)^5 ≤ (2700637070087/12500000000000 : ℝ)^4 := by
    have hnat : (2935249139 : ℕ)^5*12500000000000^4 ≤ 2700637070087^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2935249139 10000000000 2700637070087 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412002569/2000000000 : ℝ), (-880333063/1250000000 : ℝ), (2935249139/10000000000 : ℝ)] ![(13878336407379/100000000000000 : ℝ), (32258283508683/50000000000000 : ℝ), (2700637070087/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412002569/2000000000 : ℝ)|^5 ≤ (13878336407379/100000000000000 : ℝ)^4
        have hw : |(-412002569/2000000000 : ℝ)|=(412002569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-880333063/1250000000 : ℝ)|^5 ≤ (32258283508683/50000000000000 : ℝ)^4
        have hw : |(-880333063/1250000000 : ℝ)|=(880333063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2935249139/10000000000 : ℝ)|^5 ≤ (2700637070087/12500000000000 : ℝ)^4
        have hw : |(2935249139/10000000000 : ℝ)|=(2935249139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319069_s0_1 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5772705613/10000000000 : ℝ)*x 0 + (2563766097/10000000000 : ℝ)*x 1 + (792506847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5772705613/10000000000 : ℝ)^5 ≤ (6289762925697/12500000000000 : ℝ)^4 := by
    have hnat : (5772705613 : ℕ)^5*12500000000000^4 ≤ 6289762925697^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5772705613 10000000000 6289762925697 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2563766097/10000000000 : ℝ)^5 ≤ (18243073178057/100000000000000 : ℝ)^4 := by
    have hnat : (2563766097 : ℕ)^5*100000000000000^4 ≤ 18243073178057^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563766097 10000000000 18243073178057 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (792506847/2000000000 : ℝ)^5 ≤ (3929852925751/12500000000000 : ℝ)^4 := by
    have hnat : (792506847 : ℕ)^5*12500000000000^4 ≤ 3929852925751^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792506847 2000000000 3929852925751 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5772705613/10000000000 : ℝ), (2563766097/10000000000 : ℝ), (792506847/2000000000 : ℝ)] ![(6289762925697/12500000000000 : ℝ), (18243073178057/100000000000000 : ℝ), (3929852925751/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5772705613/10000000000 : ℝ)|^5 ≤ (6289762925697/12500000000000 : ℝ)^4
        have hw : |(5772705613/10000000000 : ℝ)|=(5772705613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2563766097/10000000000 : ℝ)|^5 ≤ (18243073178057/100000000000000 : ℝ)^4
        have hw : |(2563766097/10000000000 : ℝ)|=(2563766097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(792506847/2000000000 : ℝ)|^5 ≤ (3929852925751/12500000000000 : ℝ)^4
        have hw : |(792506847/2000000000 : ℝ)|=(792506847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319069_s0_2 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (946148361/2500000000 : ℝ)*x 0 + (-640793329/2000000000 : ℝ)*x 1 + (-5392551157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (946148361/2500000000 : ℝ)^5 ≤ (2968411058843/10000000000000 : ℝ)^4 := by
    have hnat : (946148361 : ℕ)^5*10000000000000^4 ≤ 2968411058843^4*2500000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946148361 2500000000 2968411058843 10000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640793329/2000000000 : ℝ)^5 ≤ (24105158015959/100000000000000 : ℝ)^4 := by
    have hnat : (640793329 : ℕ)^5*100000000000000^4 ≤ 24105158015959^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640793329 2000000000 24105158015959 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392551157/10000000000 : ℝ)^5 ≤ (11552682846061/25000000000000 : ℝ)^4 := by
    have hnat : (5392551157 : ℕ)^5*25000000000000^4 ≤ 11552682846061^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392551157 10000000000 11552682846061 25000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(946148361/2500000000 : ℝ), (-640793329/2000000000 : ℝ), (-5392551157/10000000000 : ℝ)] ![(2968411058843/10000000000000 : ℝ), (24105158015959/100000000000000 : ℝ), (11552682846061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(946148361/2500000000 : ℝ)|^5 ≤ (2968411058843/10000000000000 : ℝ)^4
        have hw : |(946148361/2500000000 : ℝ)|=(946148361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-640793329/2000000000 : ℝ)|^5 ≤ (24105158015959/100000000000000 : ℝ)^4
        have hw : |(-640793329/2000000000 : ℝ)|=(640793329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5392551157/10000000000 : ℝ)|^5 ≤ (11552682846061/25000000000000 : ℝ)^4
        have hw : |(-5392551157/10000000000 : ℝ)|=(5392551157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c319069_s0_6 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ)) (x : Fin 3 → ℝ) :
    (5772705613/10000000000 : ℝ)*x 0 + (-2563766097/10000000000 : ℝ)*x 1 + (792506847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5772705613/10000000000 : ℝ)^5 ≤ (6289762925697/12500000000000 : ℝ)^4 := by
    have hnat : (5772705613 : ℕ)^5*12500000000000^4 ≤ 6289762925697^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5772705613 10000000000 6289762925697 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2563766097/10000000000 : ℝ)^5 ≤ (18243073178057/100000000000000 : ℝ)^4 := by
    have hnat : (2563766097 : ℕ)^5*100000000000000^4 ≤ 18243073178057^4*10000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563766097 10000000000 18243073178057 100000000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (792506847/2000000000 : ℝ)^5 ≤ (3929852925751/12500000000000 : ℝ)^4 := by
    have hnat : (792506847 : ℕ)^5*12500000000000^4 ≤ 3929852925751^4*2000000000^5 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792506847 2000000000 3929852925751 12500000000000 5 4 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5 : ℝ)) 5 4 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5772705613/10000000000 : ℝ), (-2563766097/10000000000 : ℝ), (792506847/2000000000 : ℝ)] ![(6289762925697/12500000000000 : ℝ), (18243073178057/100000000000000 : ℝ), (3929852925751/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5772705613/10000000000 : ℝ)|^5 ≤ (6289762925697/12500000000000 : ℝ)^4
        have hw : |(5772705613/10000000000 : ℝ)|=(5772705613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2563766097/10000000000 : ℝ)|^5 ≤ (18243073178057/100000000000000 : ℝ)^4
        have hw : |(-2563766097/10000000000 : ℝ)|=(2563766097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(792506847/2000000000 : ℝ)|^5 ≤ (3929852925751/12500000000000 : ℝ)^4
        have hw : |(792506847/2000000000 : ℝ)|=(792506847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c319069 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1601/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(984846460225047/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1507158639512229/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (79/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^79 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^79*1^16 ≤ 1^16*1^79 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 79 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11507158639512229/10000000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11507158639512229/10000000000000000 : ℝ)^79 := by
      have hnat : (2 : ℕ)^16*10000000000000000^79 ≤ 11507158639512229^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11507158639512229 10000000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11507158639512229/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3123001274934319/2500000000000000 : ℝ) ^ (79/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3123001274934319/2500000000000000 : ℝ)^79 := by
      have hnat : (3 : ℕ)^16*2500000000000000^79 ≤ 3123001274934319^79*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3123001274934319 2500000000000000 16 79 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3123001274934319/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 79 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (79/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1507158639512229/10000000000000000 : ℝ)) (beta := (984846460225047/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1507158639512229/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(984846460225047/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-412002569/2000000000 : ℝ)*X 0 0+(-880333063/1250000000 : ℝ)*X 0 1+(2935249139/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c319069_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((5772705613/10000000000 : ℝ)*X 1 0+(2563766097/10000000000 : ℝ)*X 1 1+(792506847/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c319069_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((946148361/2500000000 : ℝ)*X 2 0+(-640793329/2000000000 : ℝ)*X 2 1+(-5392551157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c319069_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((5772705613/10000000000 : ℝ)*X 0 0+(-2563766097/10000000000 : ℝ)*X 0 1+(792506847/2000000000 : ℝ)*X 0 2+(5772705613/10000000000 : ℝ)*X 1 0+(-2563766097/10000000000 : ℝ)*X 1 1+(792506847/2000000000 : ℝ)*X 1 2+(5772705613/10000000000 : ℝ)*X 2 0+(-2563766097/10000000000 : ℝ)*X 2 1+(792506847/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c319069_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-202641/25000 : ℝ) < ((-92547/50000 : ℝ)*P 0+(-92547/50000 : ℝ)*P 1+(-92547/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-202641/25000 : ℝ) < (-20172111106820476242932180373/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (457736390847/1000000000000 : ℝ)*(base3) + (4663/250000000000 : ℝ)*(base13) + (1763/100000000000 : ℝ)*(base21) + (2387/250000000000 : ℝ)*(base24) + (15201/1000000000000 : ℝ)*(base33) + (571206673697/1000000000000 : ℝ)*(base40) + (905339332447/1000000000000 : ℝ)*(base49) + (567631197261/1000000000000 : ℝ)*(base50) + (1850939984799/1000000000000 : ℝ)*(major_s0_0) + (92547/50000 : ℝ)*(major_s0_1) + (92547/50000 : ℝ)*(major_s0_2) + (1344807397793/500000000000 : ℝ)*(sp_s0_0) + (3147351189883/1000000000000 : ℝ)*(sp_s0_1) + (2689614771859/1000000000000 : ℝ)*(sp_s0_2) + (542263609153/1000000000000 : ℝ)*(sp_s0_6) + (1344807407119/500000000000 : ℝ)*(f.sum) + (4135322539/10000000000000000000000 : ℝ)*base62 + (221974201/2000000000000000000000 : ℝ)*base65 + (2345501331/10000000000000000000000 : ℝ)*base67 + (180654881/312500000000000000000 : ℝ)*base69 + (1826338955393029/10000000000000000000000000000 : ℝ)*base70 + (5502454839060553/10000000000000000000000000000 : ℝ)*base73 + (1047372473/2000000000000000000000 : ℝ)*base74 + (2712405069393029/10000000000000000000000000000 : ℝ)*base76 + (8651944947060553/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p019_b034 (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=68 ∨ c=69 := by omega
  rcases hc with rfl|rfl
  · exact collision_c319068 p hpa (by linarith only [hpb]) X hX
  · exact collision_c319069 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (79/16 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (92547/50000 : ℝ) (17037/10000 : ℝ) (1601/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p019_b034 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

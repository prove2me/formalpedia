-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b005
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:55:32.829968+00:00
-- url     : https://prove2.me/submissions/b65e3059-2c5d-42ce-b30f-8f636404ee80

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
theorem collision_support_c324013_s0_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6980681731/10000000000 : ℝ)*x 0 + (1127578997/5000000000 : ℝ)*x 1 + (2660163203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6980681731/10000000000 : ℝ)^43 ≤ (8037617901581/12500000000000 : ℝ)^35 := by
    have hnat : (6980681731 : ℕ)^43*12500000000000^35 ≤ 8037617901581^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6980681731 10000000000 8037617901581 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127578997/5000000000 : ℝ)^43 ≤ (4011176007857/25000000000000 : ℝ)^35 := by
    have hnat : (1127578997 : ℕ)^43*25000000000000^35 ≤ 4011176007857^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127578997 5000000000 4011176007857 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2660163203/10000000000 : ℝ)^43 ≤ (19654352739743/100000000000000 : ℝ)^35 := by
    have hnat : (2660163203 : ℕ)^43*100000000000000^35 ≤ 19654352739743^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2660163203 10000000000 19654352739743 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6980681731/10000000000 : ℝ), (1127578997/5000000000 : ℝ), (2660163203/10000000000 : ℝ)] ![(8037617901581/12500000000000 : ℝ), (4011176007857/25000000000000 : ℝ), (19654352739743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6980681731/10000000000 : ℝ)|^43 ≤ (8037617901581/12500000000000 : ℝ)^35
        have hw : |(6980681731/10000000000 : ℝ)|=(6980681731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127578997/5000000000 : ℝ)|^43 ≤ (4011176007857/25000000000000 : ℝ)^35
        have hw : |(1127578997/5000000000 : ℝ)|=(1127578997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2660163203/10000000000 : ℝ)|^43 ≤ (19654352739743/100000000000000 : ℝ)^35
        have hw : |(2660163203/10000000000 : ℝ)|=(2660163203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s0_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1753401171/5000000000 : ℝ)*x 0 + (-3764875643/10000000000 : ℝ)*x 1 + (-4963004869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1753401171/5000000000 : ℝ)^43 ≤ (689971289389/2500000000000 : ℝ)^35 := by
    have hnat : (1753401171 : ℕ)^43*2500000000000^35 ≤ 689971289389^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1753401171 5000000000 689971289389 2500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3764875643/10000000000 : ℝ)^43 ≤ (30114756254233/100000000000000 : ℝ)^35 := by
    have hnat : (3764875643 : ℕ)^43*100000000000000^35 ≤ 30114756254233^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3764875643 10000000000 30114756254233 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4963004869/10000000000 : ℝ)^43 ≤ (8457278430099/20000000000000 : ℝ)^35 := by
    have hnat : (4963004869 : ℕ)^43*20000000000000^35 ≤ 8457278430099^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4963004869 10000000000 8457278430099 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1753401171/5000000000 : ℝ), (-3764875643/10000000000 : ℝ), (-4963004869/10000000000 : ℝ)] ![(689971289389/2500000000000 : ℝ), (30114756254233/100000000000000 : ℝ), (8457278430099/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1753401171/5000000000 : ℝ)|^43 ≤ (689971289389/2500000000000 : ℝ)^35
        have hw : |(1753401171/5000000000 : ℝ)|=(1753401171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3764875643/10000000000 : ℝ)|^43 ≤ (30114756254233/100000000000000 : ℝ)^35
        have hw : |(-3764875643/10000000000 : ℝ)|=(3764875643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4963004869/10000000000 : ℝ)|^43 ≤ (8457278430099/20000000000000 : ℝ)^35
        have hw : |(-4963004869/10000000000 : ℝ)|=(4963004869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s0_7 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2202099051/10000000000 : ℝ)*x 0 + (-232630173/312500000 : ℝ)*x 1 + (2115486073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2202099051/10000000000 : ℝ)^43 ≤ (3895544218169/25000000000000 : ℝ)^35 := by
    have hnat : (2202099051 : ℕ)^43*25000000000000^35 ≤ 3895544218169^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202099051 10000000000 3895544218169 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232630173/312500000 : ℝ)^43 ≤ (69585191537993/100000000000000 : ℝ)^35 := by
    have hnat : (232630173 : ℕ)^43*100000000000000^35 ≤ 69585191537993^35*312500000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232630173 312500000 69585191537993 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115486073/10000000000 : ℝ)^43 ≤ (14832631576641/100000000000000 : ℝ)^35 := by
    have hnat : (2115486073 : ℕ)^43*100000000000000^35 ≤ 14832631576641^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115486073 10000000000 14832631576641 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2202099051/10000000000 : ℝ), (-232630173/312500000 : ℝ), (2115486073/10000000000 : ℝ)] ![(3895544218169/25000000000000 : ℝ), (69585191537993/100000000000000 : ℝ), (14832631576641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2202099051/10000000000 : ℝ)|^43 ≤ (3895544218169/25000000000000 : ℝ)^35
        have hw : |(-2202099051/10000000000 : ℝ)|=(2202099051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-232630173/312500000 : ℝ)|^43 ≤ (69585191537993/100000000000000 : ℝ)^35
        have hw : |(-232630173/312500000 : ℝ)|=(232630173/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115486073/10000000000 : ℝ)|^43 ≤ (14832631576641/100000000000000 : ℝ)^35
        have hw : |(2115486073/10000000000 : ℝ)|=(2115486073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s0_8 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (828921397/1250000000 : ℝ)*x 0 + (271418257/1000000000 : ℝ)*x 1 + (2641311143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (828921397/1250000000 : ℝ)^43 ≤ (60370803651243/100000000000000 : ℝ)^35 := by
    have hnat : (828921397 : ℕ)^43*100000000000000^35 ≤ 60370803651243^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828921397 1250000000 60370803651243 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271418257/1000000000 : ℝ)^43 ≤ (1007291413199/5000000000000 : ℝ)^35 := by
    have hnat : (271418257 : ℕ)^43*5000000000000^35 ≤ 1007291413199^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271418257 1000000000 1007291413199 5000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641311143/10000000000 : ℝ)^43 ≤ (19483368075931/100000000000000 : ℝ)^35 := by
    have hnat : (2641311143 : ℕ)^43*100000000000000^35 ≤ 19483368075931^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641311143 10000000000 19483368075931 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(828921397/1250000000 : ℝ), (271418257/1000000000 : ℝ), (2641311143/10000000000 : ℝ)] ![(60370803651243/100000000000000 : ℝ), (1007291413199/5000000000000 : ℝ), (19483368075931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(828921397/1250000000 : ℝ)|^43 ≤ (60370803651243/100000000000000 : ℝ)^35
        have hw : |(828921397/1250000000 : ℝ)|=(828921397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271418257/1000000000 : ℝ)|^43 ≤ (1007291413199/5000000000000 : ℝ)^35
        have hw : |(271418257/1000000000 : ℝ)|=(271418257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641311143/10000000000 : ℝ)|^43 ≤ (19483368075931/100000000000000 : ℝ)^35
        have hw : |(2641311143/10000000000 : ℝ)|=(2641311143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s0_9 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4268924899/10000000000 : ℝ)*x 0 + (-2108197917/5000000000 : ℝ)*x 1 + (-472298121/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268924899/10000000000 : ℝ)^43 ≤ (35141467154149/100000000000000 : ℝ)^35 := by
    have hnat : (4268924899 : ℕ)^43*100000000000000^35 ≤ 35141467154149^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268924899 10000000000 35141467154149 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2108197917/5000000000 : ℝ)^43 ≤ (34610963549197/100000000000000 : ℝ)^35 := by
    have hnat : (2108197917 : ℕ)^43*100000000000000^35 ≤ 34610963549197^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108197917 5000000000 34610963549197 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (472298121/1250000000 : ℝ)^43 ≤ (15123784640671/50000000000000 : ℝ)^35 := by
    have hnat : (472298121 : ℕ)^43*50000000000000^35 ≤ 15123784640671^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472298121 1250000000 15123784640671 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268924899/10000000000 : ℝ), (-2108197917/5000000000 : ℝ), (-472298121/1250000000 : ℝ)] ![(35141467154149/100000000000000 : ℝ), (34610963549197/100000000000000 : ℝ), (15123784640671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268924899/10000000000 : ℝ)|^43 ≤ (35141467154149/100000000000000 : ℝ)^35
        have hw : |(4268924899/10000000000 : ℝ)|=(4268924899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2108197917/5000000000 : ℝ)|^43 ≤ (34610963549197/100000000000000 : ℝ)^35
        have hw : |(-2108197917/5000000000 : ℝ)|=(2108197917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-472298121/1250000000 : ℝ)|^43 ≤ (15123784640671/50000000000000 : ℝ)^35
        have hw : |(-472298121/1250000000 : ℝ)|=(472298121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s0_13 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (398997423/10000000000 : ℝ)*x 0 + (-9789/25000000 : ℝ)*x 1 + (4921833649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398997423/10000000000 : ℝ)^43 ≤ (76427880709/4000000000000 : ℝ)^35 := by
    have hnat : (398997423 : ℕ)^43*4000000000000^35 ≤ 76427880709^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398997423 10000000000 76427880709 4000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9789/25000000 : ℝ)^43 ≤ (25454783/390625000000 : ℝ)^35 := by
    have hnat : (9789 : ℕ)^43*390625000000^35 ≤ 25454783^35*25000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9789 25000000 25454783 390625000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4921833649/5000000000 : ℝ)^43 ≤ (98082786544281/100000000000000 : ℝ)^35 := by
    have hnat : (4921833649 : ℕ)^43*100000000000000^35 ≤ 98082786544281^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4921833649 5000000000 98082786544281 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(398997423/10000000000 : ℝ), (-9789/25000000 : ℝ), (4921833649/5000000000 : ℝ)] ![(76427880709/4000000000000 : ℝ), (25454783/390625000000 : ℝ), (98082786544281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(398997423/10000000000 : ℝ)|^43 ≤ (76427880709/4000000000000 : ℝ)^35
        have hw : |(398997423/10000000000 : ℝ)|=(398997423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9789/25000000 : ℝ)|^43 ≤ (25454783/390625000000 : ℝ)^35
        have hw : |(-9789/25000000 : ℝ)|=(9789/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4921833649/5000000000 : ℝ)|^43 ≤ (98082786544281/100000000000000 : ℝ)^35
        have hw : |(4921833649/5000000000 : ℝ)|=(4921833649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s0_14 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1330852911/5000000000 : ℝ)*x 0 + (-1323081523/2000000000 : ℝ)*x 1 + (1356735431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1330852911/5000000000 : ℝ)^43 ≤ (4917089073907/25000000000000 : ℝ)^35 := by
    have hnat : (1330852911 : ℕ)^43*25000000000000^35 ≤ 4917089073907^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1330852911 5000000000 4917089073907 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1323081523/2000000000 : ℝ)^43 ≤ (60192305289409/100000000000000 : ℝ)^35 := by
    have hnat : (1323081523 : ℕ)^43*100000000000000^35 ≤ 60192305289409^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323081523 2000000000 60192305289409 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356735431/5000000000 : ℝ)^43 ≤ (20139338404207/100000000000000 : ℝ)^35 := by
    have hnat : (1356735431 : ℕ)^43*100000000000000^35 ≤ 20139338404207^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356735431 5000000000 20139338404207 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1330852911/5000000000 : ℝ), (-1323081523/2000000000 : ℝ), (1356735431/5000000000 : ℝ)] ![(4917089073907/25000000000000 : ℝ), (60192305289409/100000000000000 : ℝ), (20139338404207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1330852911/5000000000 : ℝ)|^43 ≤ (4917089073907/25000000000000 : ℝ)^35
        have hw : |(-1330852911/5000000000 : ℝ)|=(1330852911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1323081523/2000000000 : ℝ)|^43 ≤ (60192305289409/100000000000000 : ℝ)^35
        have hw : |(-1323081523/2000000000 : ℝ)|=(1323081523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356735431/5000000000 : ℝ)|^43 ≤ (20139338404207/100000000000000 : ℝ)^35
        have hw : |(1356735431/5000000000 : ℝ)|=(1356735431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s0_15 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3678071891/5000000000 : ℝ)*x 0 + (277290133/1250000000 : ℝ)*x 1 + (1107877513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3678071891/5000000000 : ℝ)^43 ≤ (685757012147/1000000000000 : ℝ)^35 := by
    have hnat : (3678071891 : ℕ)^43*1000000000000^35 ≤ 685757012147^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3678071891 5000000000 685757012147 1000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277290133/1250000000 : ℝ)^43 ≤ (628932819353/4000000000000 : ℝ)^35 := by
    have hnat : (277290133 : ℕ)^43*4000000000000^35 ≤ 628932819353^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277290133 1250000000 628932819353 4000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1107877513/5000000000 : ℝ)^43 ≤ (3925244571103/25000000000000 : ℝ)^35 := by
    have hnat : (1107877513 : ℕ)^43*25000000000000^35 ≤ 3925244571103^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107877513 5000000000 3925244571103 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3678071891/5000000000 : ℝ), (277290133/1250000000 : ℝ), (1107877513/5000000000 : ℝ)] ![(685757012147/1000000000000 : ℝ), (628932819353/4000000000000 : ℝ), (3925244571103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3678071891/5000000000 : ℝ)|^43 ≤ (685757012147/1000000000000 : ℝ)^35
        have hw : |(3678071891/5000000000 : ℝ)|=(3678071891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(277290133/1250000000 : ℝ)|^43 ≤ (628932819353/4000000000000 : ℝ)^35
        have hw : |(277290133/1250000000 : ℝ)|=(277290133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1107877513/5000000000 : ℝ)|^43 ≤ (3925244571103/25000000000000 : ℝ)^35
        have hw : |(1107877513/5000000000 : ℝ)|=(1107877513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s0_16 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (122342619/312500000 : ℝ)*x 0 + (-523004083/1250000000 : ℝ)*x 1 + (-2083763371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (122342619/312500000 : ℝ)^43 ≤ (7899088154089/25000000000000 : ℝ)^35 := by
    have hnat : (122342619 : ℕ)^43*25000000000000^35 ≤ 7899088154089^35*312500000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122342619 312500000 7899088154089 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523004083/1250000000 : ℝ)^43 ≤ (34284870236943/100000000000000 : ℝ)^35 := by
    have hnat : (523004083 : ℕ)^43*100000000000000^35 ≤ 34284870236943^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523004083 1250000000 34284870236943 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083763371/5000000000 : ℝ)^43 ≤ (17059388567411/50000000000000 : ℝ)^35 := by
    have hnat : (2083763371 : ℕ)^43*50000000000000^35 ≤ 17059388567411^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083763371 5000000000 17059388567411 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(122342619/312500000 : ℝ), (-523004083/1250000000 : ℝ), (-2083763371/5000000000 : ℝ)] ![(7899088154089/25000000000000 : ℝ), (34284870236943/100000000000000 : ℝ), (17059388567411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(122342619/312500000 : ℝ)|^43 ≤ (7899088154089/25000000000000 : ℝ)^35
        have hw : |(122342619/312500000 : ℝ)|=(122342619/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523004083/1250000000 : ℝ)|^43 ≤ (34284870236943/100000000000000 : ℝ)^35
        have hw : |(-523004083/1250000000 : ℝ)|=(523004083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2083763371/5000000000 : ℝ)|^43 ≤ (17059388567411/50000000000000 : ℝ)^35
        have hw : |(-2083763371/5000000000 : ℝ)|=(2083763371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s0_20 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (182525421/10000000000 : ℝ)*x 0 + (-17039249/5000000000 : ℝ)*x 1 + (4966439787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182525421/10000000000 : ℝ)^43 ≤ (29239608033/4000000000000 : ℝ)^35 := by
    have hnat : (182525421 : ℕ)^43*4000000000000^35 ≤ 29239608033^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182525421 10000000000 29239608033 4000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17039249/5000000000 : ℝ)^43 ≤ (92998506783/100000000000000 : ℝ)^35 := by
    have hnat : (17039249 : ℕ)^43*100000000000000^35 ≤ 92998506783^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17039249 5000000000 92998506783 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4966439787/5000000000 : ℝ)^43 ≤ (19835202255703/20000000000000 : ℝ)^35 := by
    have hnat : (4966439787 : ℕ)^43*20000000000000^35 ≤ 19835202255703^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4966439787 5000000000 19835202255703 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(182525421/10000000000 : ℝ), (-17039249/5000000000 : ℝ), (4966439787/5000000000 : ℝ)] ![(29239608033/4000000000000 : ℝ), (92998506783/100000000000000 : ℝ), (19835202255703/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(182525421/10000000000 : ℝ)|^43 ≤ (29239608033/4000000000000 : ℝ)^35
        have hw : |(182525421/10000000000 : ℝ)|=(182525421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17039249/5000000000 : ℝ)|^43 ≤ (92998506783/100000000000000 : ℝ)^35
        have hw : |(-17039249/5000000000 : ℝ)|=(17039249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4966439787/5000000000 : ℝ)|^43 ≤ (19835202255703/20000000000000 : ℝ)^35
        have hw : |(4966439787/5000000000 : ℝ)|=(4966439787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s0_21 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-153218151/1000000000 : ℝ)*x 0 + (-2019787147/2500000000 : ℝ)*x 1 + (1908933643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (153218151/1000000000 : ℝ)^43 ≤ (9979192712319/100000000000000 : ℝ)^35 := by
    have hnat : (153218151 : ℕ)^43*100000000000000^35 ≤ 9979192712319^35*1000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153218151 1000000000 9979192712319 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2019787147/2500000000 : ℝ)^43 ≤ (76947057602229/100000000000000 : ℝ)^35 := by
    have hnat : (2019787147 : ℕ)^43*100000000000000^35 ≤ 76947057602229^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019787147 2500000000 76947057602229 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1908933643/10000000000 : ℝ)^43 ≤ (13073749670247/100000000000000 : ℝ)^35 := by
    have hnat : (1908933643 : ℕ)^43*100000000000000^35 ≤ 13073749670247^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908933643 10000000000 13073749670247 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-153218151/1000000000 : ℝ), (-2019787147/2500000000 : ℝ), (1908933643/10000000000 : ℝ)] ![(9979192712319/100000000000000 : ℝ), (76947057602229/100000000000000 : ℝ), (13073749670247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-153218151/1000000000 : ℝ)|^43 ≤ (9979192712319/100000000000000 : ℝ)^35
        have hw : |(-153218151/1000000000 : ℝ)|=(153218151/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2019787147/2500000000 : ℝ)|^43 ≤ (76947057602229/100000000000000 : ℝ)^35
        have hw : |(-2019787147/2500000000 : ℝ)|=(2019787147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1908933643/10000000000 : ℝ)|^43 ≤ (13073749670247/100000000000000 : ℝ)^35
        have hw : |(1908933643/10000000000 : ℝ)|=(1908933643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s0_22 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3894235453/5000000000 : ℝ)*x 0 + (1824481681/10000000000 : ℝ)*x 1 + (1013452629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3894235453/5000000000 : ℝ)^43 ≤ (36779962405277/50000000000000 : ℝ)^35 := by
    have hnat : (3894235453 : ℕ)^43*50000000000000^35 ≤ 36779962405277^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3894235453 5000000000 36779962405277 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1824481681/10000000000 : ℝ)^43 ≤ (12366793492079/100000000000000 : ℝ)^35 := by
    have hnat : (1824481681 : ℕ)^43*100000000000000^35 ≤ 12366793492079^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824481681 10000000000 12366793492079 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1013452629/5000000000 : ℝ)^43 ≤ (7036640844827/50000000000000 : ℝ)^35 := by
    have hnat : (1013452629 : ℕ)^43*50000000000000^35 ≤ 7036640844827^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013452629 5000000000 7036640844827 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3894235453/5000000000 : ℝ), (1824481681/10000000000 : ℝ), (1013452629/5000000000 : ℝ)] ![(36779962405277/50000000000000 : ℝ), (12366793492079/100000000000000 : ℝ), (7036640844827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3894235453/5000000000 : ℝ)|^43 ≤ (36779962405277/50000000000000 : ℝ)^35
        have hw : |(3894235453/5000000000 : ℝ)|=(3894235453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1824481681/10000000000 : ℝ)|^43 ≤ (12366793492079/100000000000000 : ℝ)^35
        have hw : |(1824481681/10000000000 : ℝ)|=(1824481681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1013452629/5000000000 : ℝ)|^43 ≤ (7036640844827/50000000000000 : ℝ)^35
        have hw : |(1013452629/5000000000 : ℝ)|=(1013452629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s0_23 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1584478043/5000000000 : ℝ)*x 0 + (-934608071/2500000000 : ℝ)*x 1 + (-1058773923/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1584478043/5000000000 : ℝ)^43 ≤ (24369124605673/100000000000000 : ℝ)^35 := by
    have hnat : (1584478043 : ℕ)^43*100000000000000^35 ≤ 24369124605673^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584478043 5000000000 24369124605673 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (934608071/2500000000 : ℝ)^43 ≤ (29855101448477/100000000000000 : ℝ)^35 := by
    have hnat : (934608071 : ℕ)^43*100000000000000^35 ≤ 29855101448477^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934608071 2500000000 29855101448477 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058773923/2000000000 : ℝ)^43 ≤ (11443943483507/25000000000000 : ℝ)^35 := by
    have hnat : (1058773923 : ℕ)^43*25000000000000^35 ≤ 11443943483507^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058773923 2000000000 11443943483507 25000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1584478043/5000000000 : ℝ), (-934608071/2500000000 : ℝ), (-1058773923/2000000000 : ℝ)] ![(24369124605673/100000000000000 : ℝ), (29855101448477/100000000000000 : ℝ), (11443943483507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1584478043/5000000000 : ℝ)|^43 ≤ (24369124605673/100000000000000 : ℝ)^35
        have hw : |(1584478043/5000000000 : ℝ)|=(1584478043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-934608071/2500000000 : ℝ)|^43 ≤ (29855101448477/100000000000000 : ℝ)^35
        have hw : |(-934608071/2500000000 : ℝ)|=(934608071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1058773923/2000000000 : ℝ)|^43 ≤ (11443943483507/25000000000000 : ℝ)^35
        have hw : |(-1058773923/2000000000 : ℝ)|=(1058773923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s1_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1496642289/5000000000 : ℝ)*x 0 + (-1102117229/2000000000 : ℝ)*x 1 + (917655979/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1496642289/5000000000 : ℝ)^43 ≤ (11360054484057/50000000000000 : ℝ)^35 := by
    have hnat : (1496642289 : ℕ)^43*50000000000000^35 ≤ 11360054484057^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1496642289 5000000000 11360054484057 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102117229/2000000000 : ℝ)^43 ≤ (6011087080129/12500000000000 : ℝ)^35 := by
    have hnat : (1102117229 : ℕ)^43*12500000000000^35 ≤ 6011087080129^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102117229 2000000000 6011087080129 12500000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (917655979/2500000000 : ℝ)^43 ≤ (29191194375437/100000000000000 : ℝ)^35 := by
    have hnat : (917655979 : ℕ)^43*100000000000000^35 ≤ 29191194375437^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917655979 2500000000 29191194375437 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1496642289/5000000000 : ℝ), (-1102117229/2000000000 : ℝ), (917655979/2500000000 : ℝ)] ![(11360054484057/50000000000000 : ℝ), (6011087080129/12500000000000 : ℝ), (29191194375437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1496642289/5000000000 : ℝ)|^43 ≤ (11360054484057/50000000000000 : ℝ)^35
        have hw : |(-1496642289/5000000000 : ℝ)|=(1496642289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1102117229/2000000000 : ℝ)|^43 ≤ (6011087080129/12500000000000 : ℝ)^35
        have hw : |(-1102117229/2000000000 : ℝ)|=(1102117229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(917655979/2500000000 : ℝ)|^43 ≤ (29191194375437/100000000000000 : ℝ)^35
        have hw : |(917655979/2500000000 : ℝ)|=(917655979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s1_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5484123169/10000000000 : ℝ)*x 0 + (3003592819/10000000000 : ℝ)*x 1 + (3689792377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5484123169/10000000000 : ℝ)^43 ≤ (47805136232737/100000000000000 : ℝ)^35 := by
    have hnat : (5484123169 : ℕ)^43*100000000000000^35 ≤ 47805136232737^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484123169 10000000000 47805136232737 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3003592819/10000000000 : ℝ)^43 ≤ (228162742081/1000000000000 : ℝ)^35 := by
    have hnat : (3003592819 : ℕ)^43*1000000000000^35 ≤ 228162742081^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3003592819 10000000000 228162742081 1000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3689792377/10000000000 : ℝ)^43 ≤ (29378589548669/100000000000000 : ℝ)^35 := by
    have hnat : (3689792377 : ℕ)^43*100000000000000^35 ≤ 29378589548669^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3689792377 10000000000 29378589548669 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5484123169/10000000000 : ℝ), (3003592819/10000000000 : ℝ), (3689792377/10000000000 : ℝ)] ![(47805136232737/100000000000000 : ℝ), (228162742081/1000000000000 : ℝ), (29378589548669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5484123169/10000000000 : ℝ)|^43 ≤ (47805136232737/100000000000000 : ℝ)^35
        have hw : |(5484123169/10000000000 : ℝ)|=(5484123169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3003592819/10000000000 : ℝ)|^43 ≤ (228162742081/1000000000000 : ℝ)^35
        have hw : |(3003592819/10000000000 : ℝ)|=(3003592819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3689792377/10000000000 : ℝ)|^43 ≤ (29378589548669/100000000000000 : ℝ)^35
        have hw : |(3689792377/10000000000 : ℝ)|=(3689792377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s1_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3780069849/10000000000 : ℝ)*x 0 + (-753992633/2000000000 : ℝ)*x 1 + (-587752547/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3780069849/10000000000 : ℝ)^43 ≤ (30264141324259/100000000000000 : ℝ)^35 := by
    have hnat : (3780069849 : ℕ)^43*100000000000000^35 ≤ 30264141324259^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3780069849 10000000000 30264141324259 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (753992633/2000000000 : ℝ)^43 ≤ (6032951998431/20000000000000 : ℝ)^35 := by
    have hnat : (753992633 : ℕ)^43*20000000000000^35 ≤ 6032951998431^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753992633 2000000000 6032951998431 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (587752547/1250000000 : ℝ)^43 ≤ (39571098666159/100000000000000 : ℝ)^35 := by
    have hnat : (587752547 : ℕ)^43*100000000000000^35 ≤ 39571098666159^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587752547 1250000000 39571098666159 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3780069849/10000000000 : ℝ), (-753992633/2000000000 : ℝ), (-587752547/1250000000 : ℝ)] ![(30264141324259/100000000000000 : ℝ), (6032951998431/20000000000000 : ℝ), (39571098666159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3780069849/10000000000 : ℝ)|^43 ≤ (30264141324259/100000000000000 : ℝ)^35
        have hw : |(3780069849/10000000000 : ℝ)|=(3780069849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-753992633/2000000000 : ℝ)|^43 ≤ (6032951998431/20000000000000 : ℝ)^35
        have hw : |(-753992633/2000000000 : ℝ)|=(753992633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-587752547/1250000000 : ℝ)|^43 ≤ (39571098666159/100000000000000 : ℝ)^35
        have hw : |(-587752547/1250000000 : ℝ)|=(587752547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324013_s1_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (784670733/2000000000 : ℝ)*x 0 + (-480702521/1250000000 : ℝ)*x 1 + (2245971717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (784670733/2000000000 : ℝ)^43 ≤ (31679561647387/100000000000000 : ℝ)^35 := by
    have hnat : (784670733 : ℕ)^43*100000000000000^35 ≤ 31679561647387^35*2000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784670733 2000000000 31679561647387 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (480702521/1250000000 : ℝ)^43 ≤ (15455090951891/50000000000000 : ℝ)^35 := by
    have hnat : (480702521 : ℕ)^43*50000000000000^35 ≤ 15455090951891^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480702521 1250000000 15455090951891 50000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245971717/5000000000 : ℝ)^43 ≤ (37410256439283/100000000000000 : ℝ)^35 := by
    have hnat : (2245971717 : ℕ)^43*100000000000000^35 ≤ 37410256439283^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245971717 5000000000 37410256439283 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(784670733/2000000000 : ℝ), (-480702521/1250000000 : ℝ), (2245971717/5000000000 : ℝ)] ![(31679561647387/100000000000000 : ℝ), (15455090951891/50000000000000 : ℝ), (37410256439283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(784670733/2000000000 : ℝ)|^43 ≤ (31679561647387/100000000000000 : ℝ)^35
        have hw : |(784670733/2000000000 : ℝ)|=(784670733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-480702521/1250000000 : ℝ)|^43 ≤ (15455090951891/50000000000000 : ℝ)^35
        have hw : |(-480702521/1250000000 : ℝ)|=(480702521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245971717/5000000000 : ℝ)|^43 ≤ (37410256439283/100000000000000 : ℝ)^35
        have hw : |(2245971717/5000000000 : ℝ)|=(2245971717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324013 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s0_pow0 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((6980681731/10000000000 : ℝ)*X 1 0+(1127578997/5000000000 : ℝ)*X 1 1+(2660163203/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1753401171/5000000000 : ℝ)*X 2 0+(-3764875643/10000000000 : ℝ)*X 2 1+(-4963004869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2202099051/10000000000 : ℝ)*X 0 0+(-232630173/312500000 : ℝ)*X 0 1+(2115486073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((828921397/1250000000 : ℝ)*X 1 0+(271418257/1000000000 : ℝ)*X 1 1+(2641311143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4268924899/10000000000 : ℝ)*X 2 0+(-2108197917/5000000000 : ℝ)*X 2 1+(-472298121/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((398997423/10000000000 : ℝ)*X 0 0+(-9789/25000000 : ℝ)*X 0 1+(4921833649/5000000000 : ℝ)*X 0 2+(398997423/10000000000 : ℝ)*X 1 0+(-9789/25000000 : ℝ)*X 1 1+(4921833649/5000000000 : ℝ)*X 1 2+(398997423/10000000000 : ℝ)*X 2 0+(-9789/25000000 : ℝ)*X 2 1+(4921833649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1330852911/5000000000 : ℝ)*X 0 0+(-1323081523/2000000000 : ℝ)*X 0 1+(1356735431/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((3678071891/5000000000 : ℝ)*X 1 0+(277290133/1250000000 : ℝ)*X 1 1+(1107877513/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((122342619/312500000 : ℝ)*X 2 0+(-523004083/1250000000 : ℝ)*X 2 1+(-2083763371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((182525421/10000000000 : ℝ)*X 0 0+(-17039249/5000000000 : ℝ)*X 0 1+(4966439787/5000000000 : ℝ)*X 0 2+(182525421/10000000000 : ℝ)*X 1 0+(-17039249/5000000000 : ℝ)*X 1 1+(4966439787/5000000000 : ℝ)*X 1 2+(182525421/10000000000 : ℝ)*X 2 0+(-17039249/5000000000 : ℝ)*X 2 1+(4966439787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-153218151/1000000000 : ℝ)*X 0 0+(-2019787147/2500000000 : ℝ)*X 0 1+(1908933643/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3894235453/5000000000 : ℝ)*X 1 0+(1824481681/10000000000 : ℝ)*X 1 1+(1013452629/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1584478043/5000000000 : ℝ)*X 2 0+(-934608071/2500000000 : ℝ)*X 2 1+(-1058773923/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((50723/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(50723/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6609464097856493834043/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8276753541/7812500000 : ℝ)*(base40) + (371915310157/250000000000 : ℝ)*(base50) + (387549123827/200000000000 : ℝ)*(base54) + (296449798703/1000000000000 : ℝ)*(base59) + (680637821459/125000000000 : ℝ)*(major_s0_0) + (680637821459/125000000000 : ℝ)*(major_s0_1) + (3507356952537/1000000000000 : ℝ)*(major_s0_2) + (4290587/100000000000 : ℝ)*(sp_s0_2) + (4072042154381/500000000000 : ℝ)*(sp_s0_7) + (4072045002683/500000000000 : ℝ)*(sp_s0_8) + (620617944117/100000000000 : ℝ)*(sp_s0_9) + (404183657841/500000000000 : ℝ)*(sp_s0_13) + (12203919/100000000000 : ℝ)*(sp_s0_16) + (5696603/1000000000000 : ℝ)*(sp_s0_21) + (2746112934817/1000000000000 : ℝ)*(f.failure) + (4072045002683/500000000000 : ℝ)*(f.sum) + (29732392472249/200000000000000000000000000 : ℝ)*base63 + (11390977967218747/10000000000000000000000000000 : ℝ)*base64 + (258289496430929/1250000000000000000000000000 : ℝ)*base67 + (103401395039019/1000000000000000000000000000 : ℝ)*base68 + (3707029349221387/10000000000000000000000000000 : ℝ)*base70 + (639861376444071/1250000000000000000000000000 : ℝ)*base72 + (71149317375033/125000000000000000000000000 : ℝ)*base75 + (13649452700033/125000000000000000000000000 : ℝ)*base76 + (376037221319071/625000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (13507/25000000000000000 : ℝ)*base87 + (13507/25000000000000000 : ℝ)*base89 + (13507/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-5619/12500 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-5619/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1889083162368187268709/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4079711531/100000000000 : ℝ)*(base33) + (1470142753481/1000000000000 : ℝ)*(base40) + (208322449299/200000000000 : ℝ)*(base50) + (275731747591/200000000000 : ℝ)*(base54) + (1411145952441/250000000000 : ℝ)*(major_s0_0) + (2842690462537/500000000000 : ℝ)*(major_s0_1) + (4306722187119/1000000000000 : ℝ)*(major_s0_2) + (11984091/250000000000 : ℝ)*(sp_s0_1) + (69829601/500000000000 : ℝ)*(sp_s0_2) + (111391837/500000000000 : ℝ)*(sp_s0_13) + (8503466875263/1000000000000 : ℝ)*(sp_s0_14) + (8462621823589/1000000000000 : ℝ)*(sp_s0_15) + (1770967840699/250000000000 : ℝ)*(sp_s0_16) + (744205152389/500000000000 : ℝ)*(sp_s0_20) + (358411478301/125000000000 : ℝ)*(f.failure) + (8503466875263/1000000000000 : ℝ)*(f.sum) + (5705713747317/200000000000000000000000000 : ℝ)*base63 + (4360234768440611/10000000000000000000000000000 : ℝ)*base65 + (1605487160028747/5000000000000000000000000000 : ℝ)*base67 + (361066176481453/1000000000000000000000000000 : ℝ)*base68 + (3984870220869931/10000000000000000000000000000 : ℝ)*base71 + (413745657345029/2500000000000000000000000000 : ℝ)*base72 + (135797265390981/500000000000000000000000000 : ℝ)*base74 + (241949974585733/250000000000000000000000000 : ℝ)*base77 + (1369521598338689/5000000000000000000000000000 : ℝ)*base79 + (2621/3125000000000000 : ℝ)*base87 + (2621/3125000000000000 : ℝ)*base89 + (2621/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40699/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(40699/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19703950863348104187129/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1005799646229/1000000000000 : ℝ)*(base3) + (734081780279/500000000000 : ℝ)*(base40) + (1335771/500000000000 : ℝ)*(base43) + (869338130131/500000000000 : ℝ)*(base50) + (899092850547/1000000000000 : ℝ)*(base54) + (523357077811/1000000000000 : ℝ)*(base59) + (944274259577/250000000000 : ℝ)*(major_s0_0) + (3777094366767/1000000000000 : ℝ)*(major_s0_1) + (2878004187761/1000000000000 : ℝ)*(major_s0_2) + (46618331/500000000000 : ℝ)*(sp_s0_2) + (7728299/200000000000 : ℝ)*(sp_s0_15) + (1129858468061/200000000000 : ℝ)*(sp_s0_21) + (332752800829/50000000000 : ℝ)*(sp_s0_22) + (593763281637/125000000000 : ℝ)*(sp_s0_23) + (238111562097/125000000000 : ℝ)*(f.failure) + (2824647505923/500000000000 : ℝ)*(f.sum) + (257698548354461/500000000000000000000000000 : ℝ)*base63 + (975602445514109/10000000000000000000000000000 : ℝ)*base65 + (5864199026238877/10000000000000000000000000000 : ℝ)*base67 + (20370719125107/1000000000000000000000000000 : ℝ)*base68 + (2130703437985851/10000000000000000000000000000 : ℝ)*base70 + (1463187130028987/2500000000000000000000000000 : ℝ)*base73 + (123354262165971/1000000000000000000000000000 : ℝ)*base74 + (131126748837499/250000000000000000000000000 : ℝ)*base76 + (532851819574193/400000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (2113/3125000000000000 : ℝ)*base86 + (2619/1562500000000000 : ℝ)*base88 + (2113/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (50723/100000 : ℝ) ^ (21/4 : ℝ) ≤ (1416758727643370903/50000000000000000000 : ℝ) := by
    have hpowers : (50723/100000 : ℝ)^21 ≤ (1416758727643370903/50000000000000000000 : ℝ)^4 := by
      have hnat : (50723 : ℕ)^21*50000000000000000000^4 ≤ 1416758727643370903^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50723 100000 1416758727643370903 50000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (50723/100000 : ℝ)) (X := (1416758727643370903/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (51416758727643370903/50000000000000000000 : ℝ) ≤ (10053363132260329/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (51416758727643370903/50000000000000000000 : ℝ)^4 ≤ (10053363132260329/10000000000000000 : ℝ)^21 := by
      have hnat : (51416758727643370903 : ℕ)^4*10000000000000000^21 ≤ 10053363132260329^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51416758727643370903 50000000000000000000 10053363132260329 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10053363132260329/10000000000000000 : ℝ)) (X := (51416758727643370903/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (26416758727643370903/25000000000000000000 : ℝ) ≤ (631596807454907/625000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (26416758727643370903/25000000000000000000 : ℝ)^4 ≤ (631596807454907/625000000000000 : ℝ)^21 := by
      have hnat : (26416758727643370903 : ℕ)^4*625000000000000^21 ≤ 631596807454907^21*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26416758727643370903 25000000000000000000 631596807454907 625000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (631596807454907/625000000000000 : ℝ)) (X := (26416758727643370903/25000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(53363132260329/5072300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(52185787018183/5072300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (50723/100000 : ℝ)) (alpha := (53363132260329/5072300000000000 : ℝ)) (beta := (52185787018183/5072300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (50723/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(53363132260329/5072300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(52185787018183/5072300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (5619/12500 : ℝ) ^ (21/4 : ℝ) ≤ (751453920396008609/50000000000000000000 : ℝ) := by
    have hpowers : (5619/12500 : ℝ)^21 ≤ (751453920396008609/50000000000000000000 : ℝ)^4 := by
      have hnat : (5619 : ℕ)^21*50000000000000000000^4 ≤ 751453920396008609^4*12500^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5619 12500 751453920396008609 50000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5619/12500 : ℝ)) (X := (751453920396008609/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (50751453920396008609/50000000000000000000 : ℝ) ≤ (1002845423556819/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (50751453920396008609/50000000000000000000 : ℝ)^4 ≤ (1002845423556819/1000000000000000 : ℝ)^21 := by
      have hnat : (50751453920396008609 : ℕ)^4*1000000000000000^21 ≤ 1002845423556819^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50751453920396008609 50000000000000000000 1002845423556819 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002845423556819/1000000000000000 : ℝ)) (X := (50751453920396008609/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25751453920396008609/25000000000000000000 : ℝ) ≤ (10056569430001211/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (25751453920396008609/25000000000000000000 : ℝ)^4 ≤ (10056569430001211/10000000000000000 : ℝ)^21 := by
      have hnat : (25751453920396008609 : ℕ)^4*10000000000000000^21 ≤ 10056569430001211^21*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25751453920396008609 25000000000000000000 10056569430001211 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10056569430001211/10000000000000000 : ℝ)) (X := (25751453920396008609/25000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(2845423556819/449520000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(28115194433021/4495200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (5619/12500 : ℝ)) (alpha := (2845423556819/449520000000000 : ℝ)) (beta := (28115194433021/4495200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (5619/12500 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(2845423556819/449520000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(28115194433021/4495200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (40699/100000 : ℝ) ^ (21/4 : ℝ) ≤ (445948421786534781/50000000000000000000 : ℝ) := by
    have hpowers : (40699/100000 : ℝ)^21 ≤ (445948421786534781/50000000000000000000 : ℝ)^4 := by
      have hnat : (40699 : ℕ)^21*50000000000000000000^4 ≤ 445948421786534781^4*100000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40699 100000 445948421786534781 50000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40699/100000 : ℝ)) (X := (445948421786534781/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50445948421786534781/50000000000000000000 : ℝ) ≤ (10016927509665127/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (50445948421786534781/50000000000000000000 : ℝ)^4 ≤ (10016927509665127/10000000000000000 : ℝ)^21 := by
      have hnat : (50445948421786534781 : ℕ)^4*10000000000000000^21 ≤ 10016927509665127^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50445948421786534781 50000000000000000000 10016927509665127 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016927509665127/10000000000000000 : ℝ)) (X := (50445948421786534781/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25445948421786534781/25000000000000000000 : ℝ) ≤ (313554197230299/312500000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (25445948421786534781/25000000000000000000 : ℝ)^4 ≤ (313554197230299/312500000000000 : ℝ)^21 := by
      have hnat : (25445948421786534781 : ℕ)^4*312500000000000^21 ≤ 313554197230299^21*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25445948421786534781 25000000000000000000 313554197230299 312500000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (313554197230299/312500000000000 : ℝ)) (X := (25445948421786534781/25000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(16927509665127/4069900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(16806801704441/4069900000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (40699/100000 : ℝ)) (alpha := (16927509665127/4069900000000000 : ℝ)) (beta := (16806801704441/4069900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (40699/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(16927509665127/4069900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(16806801704441/4069900000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1496642289/5000000000 : ℝ)*X 0 0+(-1102117229/2000000000 : ℝ)*X 0 1+(917655979/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5484123169/10000000000 : ℝ)*X 1 0+(3003592819/10000000000 : ℝ)*X 1 1+(3689792377/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3780069849/10000000000 : ℝ)*X 2 0+(-753992633/2000000000 : ℝ)*X 2 1+(-587752547/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((784670733/2000000000 : ℝ)*X 0 0+(-480702521/1250000000 : ℝ)*X 0 1+(2245971717/5000000000 : ℝ)*X 0 2+(784670733/2000000000 : ℝ)*X 1 0+(-480702521/1250000000 : ℝ)*X 1 1+(2245971717/5000000000 : ℝ)*X 1 2+(784670733/2000000000 : ℝ)*X 2 0+(-480702521/1250000000 : ℝ)*X 2 1+(2245971717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324013_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-111213/12500 : ℝ) < ((-49571/25000 : ℝ)*P 0+(-49571/25000 : ℝ)*P 1+(-49571/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-111213/12500 : ℝ) < (-332351586156157302061591253284059/38001671600000000000000000000000 : ℝ) := by norm_num
    linear_combination (36043/500000000000 : ℝ)*(base3) + (877/500000000000 : ℝ)*(base10) + (52077/500000000000 : ℝ)*(base24) + (14949504127/31250000000 : ℝ)*(base40) + (13423/1000000000000 : ℝ)*(base43) + (31061/500000000000 : ℝ)*(base49) + (475973717963/1000000000000 : ℝ)*(base50) + (2019/200000000000 : ℝ)*(ratio_s0_2) + (49571/25000 : ℝ)*(major_s1_0) + (1982839986577/1000000000000 : ℝ)*(major_s1_1) + (49571/25000 : ℝ)*(major_s1_2) + (2915236535941/1000000000000 : ℝ)*(sp_s1_0) + (728809155801/250000000000 : ℝ)*(sp_s1_1) + (2915236433541/1000000000000 : ℝ)*(sp_s1_2) + (499999963957/500000000000 : ℝ)*(sp_s1_6) + (1457618275559/500000000000 : ℝ)*(f.sum) + (5159218293193344113/18295014480000000000000000000000 : ℝ)*base62 + (78314262929097/406990000000000000000000000 : ℝ)*base64 + (3860598393657523/4495200000000000000000000000 : ℝ)*base66 + (39131930439043/203495000000000000000000000 : ℝ)*base69 + (1938691871989087113/5160938442500000000000000000000 : ℝ)*base71 + (19956413694779/63403750000000000000000000 : ℝ)*base72 + (234404314887851/449520000000000000000000000 : ℝ)*base74 + (73959134618691/507230000000000000000000000 : ℝ)*base77 + (240109440101169278009/228010029600000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c324014_s0_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1457352381/5000000000 : ℝ)*x 0 + (-4647217561/10000000000 : ℝ)*x 1 + (-1161804377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1457352381/5000000000 : ℝ)^43 ≤ (21989542136299/100000000000000 : ℝ)^35 := by
    have hnat : (1457352381 : ℕ)^43*100000000000000^35 ≤ 21989542136299^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1457352381 5000000000 21989542136299 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4647217561/10000000000 : ℝ)^43 ≤ (7801045839913/20000000000000 : ℝ)^35 := by
    have hnat : (4647217561 : ℕ)^43*20000000000000^35 ≤ 7801045839913^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4647217561 10000000000 7801045839913 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1161804377/2500000000 : ℝ)^43 ≤ (7801045730609/20000000000000 : ℝ)^35 := by
    have hnat : (1161804377 : ℕ)^43*20000000000000^35 ≤ 7801045730609^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161804377 2500000000 7801045730609 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1457352381/5000000000 : ℝ), (-4647217561/10000000000 : ℝ), (-1161804377/2500000000 : ℝ)] ![(21989542136299/100000000000000 : ℝ), (7801045839913/20000000000000 : ℝ), (7801045730609/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1457352381/5000000000 : ℝ)|^43 ≤ (21989542136299/100000000000000 : ℝ)^35
        have hw : |(-1457352381/5000000000 : ℝ)|=(1457352381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4647217561/10000000000 : ℝ)|^43 ≤ (7801045839913/20000000000000 : ℝ)^35
        have hw : |(-4647217561/10000000000 : ℝ)|=(4647217561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1161804377/2500000000 : ℝ)|^43 ≤ (7801045730609/20000000000000 : ℝ)^35
        have hw : |(-1161804377/2500000000 : ℝ)|=(1161804377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324014_s0_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1442546521/2500000000 : ℝ)*x 0 + (3188788667/10000000000 : ℝ)*x 1 + (-398598579/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1442546521/2500000000 : ℝ)^43 ≤ (50886740659481/100000000000000 : ℝ)^35 := by
    have hnat : (1442546521 : ℕ)^43*100000000000000^35 ≤ 50886740659481^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1442546521 2500000000 50886740659481 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3188788667/10000000000 : ℝ)^43 ≤ (24556629830331/100000000000000 : ℝ)^35 := by
    have hnat : (3188788667 : ℕ)^43*100000000000000^35 ≤ 24556629830331^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3188788667 10000000000 24556629830331 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398598579/1250000000 : ℝ)^43 ≤ (24556629499191/100000000000000 : ℝ)^35 := by
    have hnat : (398598579 : ℕ)^43*100000000000000^35 ≤ 24556629499191^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398598579 1250000000 24556629499191 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1442546521/2500000000 : ℝ), (3188788667/10000000000 : ℝ), (-398598579/1250000000 : ℝ)] ![(50886740659481/100000000000000 : ℝ), (24556629830331/100000000000000 : ℝ), (24556629499191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1442546521/2500000000 : ℝ)|^43 ≤ (50886740659481/100000000000000 : ℝ)^35
        have hw : |(1442546521/2500000000 : ℝ)|=(1442546521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3188788667/10000000000 : ℝ)|^43 ≤ (24556629830331/100000000000000 : ℝ)^35
        have hw : |(3188788667/10000000000 : ℝ)|=(3188788667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-398598579/1250000000 : ℝ)|^43 ≤ (24556629499191/100000000000000 : ℝ)^35
        have hw : |(-398598579/1250000000 : ℝ)|=(398598579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324014_s0_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1457352381/5000000000 : ℝ)*x 0 + (-4647217561/10000000000 : ℝ)*x 1 + (1161804377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1457352381/5000000000 : ℝ)^43 ≤ (21989542136299/100000000000000 : ℝ)^35 := by
    have hnat : (1457352381 : ℕ)^43*100000000000000^35 ≤ 21989542136299^35*5000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1457352381 5000000000 21989542136299 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4647217561/10000000000 : ℝ)^43 ≤ (7801045839913/20000000000000 : ℝ)^35 := by
    have hnat : (4647217561 : ℕ)^43*20000000000000^35 ≤ 7801045839913^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4647217561 10000000000 7801045839913 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1161804377/2500000000 : ℝ)^43 ≤ (7801045730609/20000000000000 : ℝ)^35 := by
    have hnat : (1161804377 : ℕ)^43*20000000000000^35 ≤ 7801045730609^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161804377 2500000000 7801045730609 20000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1457352381/5000000000 : ℝ), (-4647217561/10000000000 : ℝ), (1161804377/2500000000 : ℝ)] ![(21989542136299/100000000000000 : ℝ), (7801045839913/20000000000000 : ℝ), (7801045730609/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1457352381/5000000000 : ℝ)|^43 ≤ (21989542136299/100000000000000 : ℝ)^35
        have hw : |(1457352381/5000000000 : ℝ)|=(1457352381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4647217561/10000000000 : ℝ)|^43 ≤ (7801045839913/20000000000000 : ℝ)^35
        have hw : |(-4647217561/10000000000 : ℝ)|=(4647217561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1161804377/2500000000 : ℝ)|^43 ≤ (7801045730609/20000000000000 : ℝ)^35
        have hw : |(1161804377/2500000000 : ℝ)|=(1161804377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324014_s0_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1442546521/2500000000 : ℝ)*x 0 + (-3188788667/10000000000 : ℝ)*x 1 + (-398598579/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1442546521/2500000000 : ℝ)^43 ≤ (50886740659481/100000000000000 : ℝ)^35 := by
    have hnat : (1442546521 : ℕ)^43*100000000000000^35 ≤ 50886740659481^35*2500000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1442546521 2500000000 50886740659481 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3188788667/10000000000 : ℝ)^43 ≤ (24556629830331/100000000000000 : ℝ)^35 := by
    have hnat : (3188788667 : ℕ)^43*100000000000000^35 ≤ 24556629830331^35*10000000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3188788667 10000000000 24556629830331 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398598579/1250000000 : ℝ)^43 ≤ (24556629499191/100000000000000 : ℝ)^35 := by
    have hnat : (398598579 : ℕ)^43*100000000000000^35 ≤ 24556629499191^35*1250000000^43 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398598579 1250000000 24556629499191 100000000000000 43 35 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (43/8 : ℝ)) 43 35 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1442546521/2500000000 : ℝ), (-3188788667/10000000000 : ℝ), (-398598579/1250000000 : ℝ)] ![(50886740659481/100000000000000 : ℝ), (24556629830331/100000000000000 : ℝ), (24556629499191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1442546521/2500000000 : ℝ)|^43 ≤ (50886740659481/100000000000000 : ℝ)^35
        have hw : |(1442546521/2500000000 : ℝ)|=(1442546521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3188788667/10000000000 : ℝ)|^43 ≤ (24556629830331/100000000000000 : ℝ)^35
        have hw : |(-3188788667/10000000000 : ℝ)|=(3188788667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-398598579/1250000000 : ℝ)|^43 ≤ (24556629499191/100000000000000 : ℝ)^35
        have hw : |(-398598579/1250000000 : ℝ)|=(398598579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324014 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (43/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81117/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81117/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (21/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^21 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^21*1^4 ≤ 1^4*1^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (1141140309994013/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (1141140309994013/1000000000000000 : ℝ)^21 := by
      have hnat : (2 : ℕ)^4*1000000000000000^21 ≤ 1141140309994013^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 1141140309994013 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1141140309994013/1000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12327648392357461/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12327648392357461/10000000000000000 : ℝ)^21 := by
      have hnat : (3 : ℕ)^4*10000000000000000^21 ≤ 12327648392357461^21*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12327648392357461 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12327648392357461/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1457352381/5000000000 : ℝ)*X 0 0+(-4647217561/10000000000 : ℝ)*X 0 1+(-1161804377/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324014_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1442546521/2500000000 : ℝ)*X 1 0+(3188788667/10000000000 : ℝ)*X 1 1+(-398598579/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324014_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1457352381/5000000000 : ℝ)*X 2 0+(-4647217561/10000000000 : ℝ)*X 2 1+(1161804377/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324014_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1442546521/2500000000 : ℝ)*X 0 0+(-3188788667/10000000000 : ℝ)*X 0 1+(-398598579/1250000000 : ℝ)*X 0 2+(1442546521/2500000000 : ℝ)*X 1 0+(-3188788667/10000000000 : ℝ)*X 1 1+(-398598579/1250000000 : ℝ)*X 1 2+(1442546521/2500000000 : ℝ)*X 2 0+(-3188788667/10000000000 : ℝ)*X 2 1+(-398598579/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324014_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-111213/12500 : ℝ) < ((-49571/25000 : ℝ)*P 0+(-49571/25000 : ℝ)*P 1+(-49571/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-111213/12500 : ℝ) < (-10955106308648460187234692429/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1443/62500000000 : ℝ)*(base12) + (577206016419/1000000000000 : ℝ)*(base39) + (6620538939/250000000000 : ℝ)*(base40) + (49892010699/125000000000 : ℝ)*(base49) + (54894411999/200000000000 : ℝ)*(base50) + (773/100000000000 : ℝ)*(base53) + (31166010373/250000000000 : ℝ)*(base59) + (49571/25000 : ℝ)*(major_s0_0) + (3872734381/1953125000 : ℝ)*(major_s0_1) + (198283999227/100000000000 : ℝ)*(major_s0_2) + (2921361645341/1000000000000 : ℝ)*(sp_s0_0) + (2921361665357/1000000000000 : ℝ)*(sp_s0_1) + (2921361676159/1000000000000 : ℝ)*(sp_s0_2) + (1 : ℝ)*(sp_s0_6) + (2921361673087/1000000000000 : ℝ)*(f.sum) + (179576414435787/500000000000000000000000000 : ℝ)*base63 + (524647704496863/1000000000000000000000000000 : ℝ)*base64 + (38546752242347/39062500000000000000000000 : ℝ)*base67 + (11151146747951/100000000000000000000000000 : ℝ)*base69 + (84374973503137/1000000000000000000000000000 : ℝ)*base71 + (69674323/312500000000000000000 : ℝ)*base72 + (6161154103001/15625000000000000000000000 : ℝ)*base75 + (3787197399/10000000000000000000000 : ℝ)*base77 + (7561510211097/39062500000000000000000000 : ℝ)*base79 + (3/976562500 : ℝ)*base81 + (3/976562500 : ℝ)*base85 + (3/976562500 : ℝ)*base88 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p024_b005 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 13 ≤ c.val) (hhi : c.val < 15)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=13 ∨ c=14 := by omega
  rcases hc with rfl|rfl
  · exact collision_c324013 p hpa (by linarith only [hpb]) X hX
  · exact collision_c324014 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 13 ≤ c.val) (hhi : c.val < 15)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b005 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

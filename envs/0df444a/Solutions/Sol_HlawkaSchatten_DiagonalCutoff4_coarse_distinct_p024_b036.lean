-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b036
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:57:15.807748+00:00
-- url     : https://prove2.me/submissions/85fddeba-ed1f-4fbe-8f41-b01e71043913

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
theorem collision_support_c324070_s0_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-67792747/312500000 : ℝ)*x 0 + (-3857894217/10000000000 : ℝ)*x 1 + (-6050012587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67792747/312500000 : ℝ)^85 ≤ (7610434744719/50000000000000 : ℝ)^69 := by
    have hnat : (67792747 : ℕ)^85*50000000000000^69 ≤ 7610434744719^69*312500000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67792747 312500000 7610434744719 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3857894217/10000000000 : ℝ)^85 ≤ (30933677087201/100000000000000 : ℝ)^69 := by
    have hnat : (3857894217 : ℕ)^85*100000000000000^69 ≤ 30933677087201^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3857894217 10000000000 30933677087201 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6050012587/10000000000 : ℝ)^85 ≤ (53845453414583/100000000000000 : ℝ)^69 := by
    have hnat : (6050012587 : ℕ)^85*100000000000000^69 ≤ 53845453414583^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6050012587 10000000000 53845453414583 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67792747/312500000 : ℝ), (-3857894217/10000000000 : ℝ), (-6050012587/10000000000 : ℝ)] ![(7610434744719/50000000000000 : ℝ), (30933677087201/100000000000000 : ℝ), (53845453414583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67792747/312500000 : ℝ)|^85 ≤ (7610434744719/50000000000000 : ℝ)^69
        have hw : |(-67792747/312500000 : ℝ)|=(67792747/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3857894217/10000000000 : ℝ)|^85 ≤ (30933677087201/100000000000000 : ℝ)^69
        have hw : |(-3857894217/10000000000 : ℝ)|=(3857894217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6050012587/10000000000 : ℝ)|^85 ≤ (53845453414583/100000000000000 : ℝ)^69
        have hw : |(-6050012587/10000000000 : ℝ)|=(6050012587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324070_s0_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6050012599/10000000000 : ℝ)*x 0 + (1928947089/5000000000 : ℝ)*x 1 + (-542341983/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6050012599/10000000000 : ℝ)^85 ≤ (53845453546149/100000000000000 : ℝ)^69 := by
    have hnat : (6050012599 : ℕ)^85*100000000000000^69 ≤ 53845453546149^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6050012599 10000000000 53845453546149 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1928947089/5000000000 : ℝ)^85 ≤ (1237347068079/4000000000000 : ℝ)^69 := by
    have hnat : (1928947089 : ℕ)^85*4000000000000^69 ≤ 1237347068079^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928947089 5000000000 1237347068079 4000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542341983/2500000000 : ℝ)^85 ≤ (15220869731449/100000000000000 : ℝ)^69 := by
    have hnat : (542341983 : ℕ)^85*100000000000000^69 ≤ 15220869731449^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542341983 2500000000 15220869731449 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6050012599/10000000000 : ℝ), (1928947089/5000000000 : ℝ), (-542341983/2500000000 : ℝ)] ![(53845453546149/100000000000000 : ℝ), (1237347068079/4000000000000 : ℝ), (15220869731449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6050012599/10000000000 : ℝ)|^85 ≤ (53845453546149/100000000000000 : ℝ)^69
        have hw : |(6050012599/10000000000 : ℝ)|=(6050012599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1928947089/5000000000 : ℝ)|^85 ≤ (1237347068079/4000000000000 : ℝ)^69
        have hw : |(1928947089/5000000000 : ℝ)|=(1928947089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-542341983/2500000000 : ℝ)|^85 ≤ (15220869731449/100000000000000 : ℝ)^69
        have hw : |(-542341983/2500000000 : ℝ)|=(542341983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324070_s0_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (454723491/1250000000 : ℝ)*x 0 + (-199525441/400000000 : ℝ)*x 1 + (3637788011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (454723491/1250000000 : ℝ)^85 ≤ (2877415418223/10000000000000 : ℝ)^69 := by
    have hnat : (454723491 : ℕ)^85*10000000000000^69 ≤ 2877415418223^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454723491 1250000000 2877415418223 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199525441/400000000 : ℝ)^85 ≤ (10612922704217/25000000000000 : ℝ)^69 := by
    have hnat : (199525441 : ℕ)^85*25000000000000^69 ≤ 10612922704217^69*400000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199525441 400000000 10612922704217 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3637788011/10000000000 : ℝ)^85 ≤ (14387077495489/50000000000000 : ℝ)^69 := by
    have hnat : (3637788011 : ℕ)^85*50000000000000^69 ≤ 14387077495489^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3637788011 10000000000 14387077495489 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(454723491/1250000000 : ℝ), (-199525441/400000000 : ℝ), (3637788011/10000000000 : ℝ)] ![(2877415418223/10000000000000 : ℝ), (10612922704217/25000000000000 : ℝ), (14387077495489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(454723491/1250000000 : ℝ)|^85 ≤ (2877415418223/10000000000000 : ℝ)^69
        have hw : |(454723491/1250000000 : ℝ)|=(454723491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-199525441/400000000 : ℝ)|^85 ≤ (10612922704217/25000000000000 : ℝ)^69
        have hw : |(-199525441/400000000 : ℝ)|=(199525441/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3637788011/10000000000 : ℝ)|^85 ≤ (14387077495489/50000000000000 : ℝ)^69
        have hw : |(3637788011/10000000000 : ℝ)|=(3637788011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324070_s0_3 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9999999939/10000000000 : ℝ)*x 0 + (2509/10000000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9999999939/10000000000 : ℝ)^85 ≤ (99999999248551/100000000000000 : ℝ)^69 := by
    have hnat : (9999999939 : ℕ)^85*100000000000000^69 ≤ 99999999248551^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999939 10000000000 99999999248551 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2509/10000000000 : ℝ)^85 ≤ (739521/100000000000000 : ℝ)^69 := by
    have hnat : (2509 : ℕ)^85*100000000000000^69 ≤ 739521^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509 10000000000 739521 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^85 ≤ (0 : ℝ)^69 := by
    have hnat : (0 : ℕ)^85*1^69 ≤ 0^69*1^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9999999939/10000000000 : ℝ), (2509/10000000000 : ℝ), (0 : ℝ)] ![(99999999248551/100000000000000 : ℝ), (739521/100000000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9999999939/10000000000 : ℝ)|^85 ≤ (99999999248551/100000000000000 : ℝ)^69
        have hw : |(9999999939/10000000000 : ℝ)|=(9999999939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2509/10000000000 : ℝ)|^85 ≤ (739521/100000000000000 : ℝ)^69
        have hw : |(2509/10000000000 : ℝ)|=(2509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^85 ≤ (0 : ℝ)^69
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324070_s0_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1221245567/2500000000 : ℝ)*x 0 + (-120091103/500000000 : ℝ)*x 1 + (-4884982209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1221245567/2500000000 : ℝ)^85 ≤ (10343208710681/25000000000000 : ℝ)^69 := by
    have hnat : (1221245567 : ℕ)^85*25000000000000^69 ≤ 10343208710681^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221245567 2500000000 10343208710681 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120091103/500000000 : ℝ)^85 ≤ (8627165460803/50000000000000 : ℝ)^69 := by
    have hnat : (120091103 : ℕ)^85*50000000000000^69 ≤ 8627165460803^69*500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120091103 500000000 8627165460803 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4884982209/10000000000 : ℝ)^85 ≤ (41372834227159/100000000000000 : ℝ)^69 := by
    have hnat : (4884982209 : ℕ)^85*100000000000000^69 ≤ 41372834227159^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4884982209 10000000000 41372834227159 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1221245567/2500000000 : ℝ), (-120091103/500000000 : ℝ), (-4884982209/10000000000 : ℝ)] ![(10343208710681/25000000000000 : ℝ), (8627165460803/50000000000000 : ℝ), (41372834227159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1221245567/2500000000 : ℝ)|^85 ≤ (10343208710681/25000000000000 : ℝ)^69
        have hw : |(1221245567/2500000000 : ℝ)|=(1221245567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-120091103/500000000 : ℝ)|^85 ≤ (8627165460803/50000000000000 : ℝ)^69
        have hw : |(-120091103/500000000 : ℝ)|=(120091103/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4884982209/10000000000 : ℝ)|^85 ≤ (41372834227159/100000000000000 : ℝ)^69
        have hw : |(-4884982209/10000000000 : ℝ)|=(4884982209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324070 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-67792747/312500000 : ℝ)*X 0 0+(-3857894217/10000000000 : ℝ)*X 0 1+(-6050012587/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324070_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((6050012599/10000000000 : ℝ)*X 1 0+(1928947089/5000000000 : ℝ)*X 1 1+(-542341983/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324070_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((454723491/1250000000 : ℝ)*X 2 0+(-199525441/400000000 : ℝ)*X 2 1+(3637788011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324070_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((9999999939/10000000000 : ℝ)*X 1 0+(2509/10000000000 : ℝ)*X 1 1+(9999999939/10000000000 : ℝ)*X 2 0+(2509/10000000000 : ℝ)*X 2 1+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324070_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1221245567/2500000000 : ℝ)*X 0 0+(-120091103/500000000 : ℝ)*X 0 1+(-4884982209/10000000000 : ℝ)*X 0 2+(1221245567/2500000000 : ℝ)*X 1 0+(-120091103/500000000 : ℝ)*X 1 1+(-4884982209/10000000000 : ℝ)*X 1 2+(1221245567/2500000000 : ℝ)*X 2 0+(-120091103/500000000 : ℝ)*X 2 1+(-4884982209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324070_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-111213/12500 : ℝ) < ((-49571/25000 : ℝ)*P 0+(-49571/25000 : ℝ)*P 1+(-49571/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-111213/12500 : ℝ) < (-43988349338678884058946724359/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9697/1000000000000 : ℝ)*(base3) + (9529/1000000000000 : ℝ)*(base21) + (21140174027/31250000000 : ℝ)*(base39) + (25357/1000000000000 : ℝ)*(base43) + (122931546941/500000000000 : ℝ)*(base49) + (214815851357/500000000000 : ℝ)*(base59) + (3381/125000000000 : ℝ)*(base60) + (123927501179/62500000000 : ℝ)*(major_s0_0) + (1982839974643/1000000000000 : ℝ)*(major_s0_1) + (49571/25000 : ℝ)*(major_s0_2) + (2932556597219/1000000000000 : ℝ)*(sp_s0_0) + (2932556632273/1000000000000 : ℝ)*(sp_s0_1) + (293255658769/100000000000 : ℝ)*(sp_s0_2) + (1179/62500000000 : ℝ)*(sp_s0_3) + (999999990303/1000000000000 : ℝ)*(sp_s0_6) + (183284788911/62500000000 : ℝ)*(f.sum) + (1765960758262167/10000000000000000000000000000 : ℝ)*base63 + (7309533257/10000000000000000000000 : ℝ)*base64 + (117224913812359/1000000000000000000000000000 : ℝ)*base66 + (2301565173/10000000000000000000000 : ℝ)*base69 + (31458785496173/62500000000000000000000000 : ℝ)*base70 + (117388439779251/625000000000000000000000000 : ℝ)*base72 + (570076966262167/10000000000000000000000000000 : ℝ)*base75 + (18499167971173/62500000000000000000000000 : ℝ)*base76 + (1465916540295803/5000000000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c324071_s0_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3533431551/10000000000 : ℝ)*x 0 + (2524956969/5000000000 : ℝ)*x 1 + (1837592627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3533431551/10000000000 : ℝ)^85 ≤ (27760718099543/100000000000000 : ℝ)^69 := by
    have hnat : (3533431551 : ℕ)^85*100000000000000^69 ≤ 27760718099543^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3533431551 10000000000 27760718099543 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2524956969/5000000000 : ℝ)^85 ≤ (21550148422817/50000000000000 : ℝ)^69 := by
    have hnat : (2524956969 : ℕ)^85*50000000000000^69 ≤ 21550148422817^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2524956969 5000000000 21550148422817 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1837592627/5000000000 : ℝ)^85 ≤ (29138985029527/100000000000000 : ℝ)^69 := by
    have hnat : (1837592627 : ℕ)^85*100000000000000^69 ≤ 29138985029527^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837592627 5000000000 29138985029527 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3533431551/10000000000 : ℝ), (2524956969/5000000000 : ℝ), (1837592627/5000000000 : ℝ)] ![(27760718099543/100000000000000 : ℝ), (21550148422817/50000000000000 : ℝ), (29138985029527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3533431551/10000000000 : ℝ)|^85 ≤ (27760718099543/100000000000000 : ℝ)^69
        have hw : |(3533431551/10000000000 : ℝ)|=(3533431551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2524956969/5000000000 : ℝ)|^85 ≤ (21550148422817/50000000000000 : ℝ)^69
        have hw : |(2524956969/5000000000 : ℝ)|=(2524956969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1837592627/5000000000 : ℝ)|^85 ≤ (29138985029527/100000000000000 : ℝ)^69
        have hw : |(1837592627/5000000000 : ℝ)|=(1837592627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s0_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1250002187/2000000000 : ℝ)*x 0 + (-715170913/2000000000 : ℝ)*x 1 + (-446803981/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1250002187/2000000000 : ℝ)^85 ≤ (56046536985769/100000000000000 : ℝ)^69 := by
    have hnat : (1250002187 : ℕ)^85*100000000000000^69 ≤ 56046536985769^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250002187 2000000000 56046536985769 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (715170913/2000000000 : ℝ)^85 ≤ (5634375012453/20000000000000 : ℝ)^69 := by
    have hnat : (715170913 : ℕ)^85*20000000000000^69 ≤ 5634375012453^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715170913 2000000000 5634375012453 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (446803981/2000000000 : ℝ)^85 ≤ (15781587929531/100000000000000 : ℝ)^69 := by
    have hnat : (446803981 : ℕ)^85*100000000000000^69 ≤ 15781587929531^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446803981 2000000000 15781587929531 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1250002187/2000000000 : ℝ), (-715170913/2000000000 : ℝ), (-446803981/2000000000 : ℝ)] ![(56046536985769/100000000000000 : ℝ), (5634375012453/20000000000000 : ℝ), (15781587929531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1250002187/2000000000 : ℝ)|^85 ≤ (56046536985769/100000000000000 : ℝ)^69
        have hw : |(1250002187/2000000000 : ℝ)|=(1250002187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-715170913/2000000000 : ℝ)|^85 ≤ (5634375012453/20000000000000 : ℝ)^69
        have hw : |(-715170913/2000000000 : ℝ)|=(715170913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-446803981/2000000000 : ℝ)|^85 ≤ (15781587929531/100000000000000 : ℝ)^69
        have hw : |(-446803981/2000000000 : ℝ)|=(446803981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s0_7 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3758479401/10000000000 : ℝ)*x 0 + (-4699654303/10000000000 : ℝ)*x 1 + (1911912901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3758479401/10000000000 : ℝ)^85 ≤ (3744331450443/12500000000000 : ℝ)^69 := by
    have hnat : (3758479401 : ℕ)^85*12500000000000^69 ≤ 3744331450443^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3758479401 10000000000 3744331450443 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4699654303/10000000000 : ℝ)^85 ≤ (39447839862589/100000000000000 : ℝ)^69 := by
    have hnat : (4699654303 : ℕ)^85*100000000000000^69 ≤ 39447839862589^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4699654303 10000000000 39447839862589 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1911912901/5000000000 : ℝ)^85 ≤ (30597508522807/100000000000000 : ℝ)^69 := by
    have hnat : (1911912901 : ℕ)^85*100000000000000^69 ≤ 30597508522807^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911912901 5000000000 30597508522807 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3758479401/10000000000 : ℝ), (-4699654303/10000000000 : ℝ), (1911912901/5000000000 : ℝ)] ![(3744331450443/12500000000000 : ℝ), (39447839862589/100000000000000 : ℝ), (30597508522807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3758479401/10000000000 : ℝ)|^85 ≤ (3744331450443/12500000000000 : ℝ)^69
        have hw : |(-3758479401/10000000000 : ℝ)|=(3758479401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4699654303/10000000000 : ℝ)|^85 ≤ (39447839862589/100000000000000 : ℝ)^69
        have hw : |(-4699654303/10000000000 : ℝ)|=(4699654303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1911912901/5000000000 : ℝ)|^85 ≤ (30597508522807/100000000000000 : ℝ)^69
        have hw : |(1911912901/5000000000 : ℝ)|=(1911912901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s0_8 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (335754211/1000000000 : ℝ)*x 0 + (2613055057/5000000000 : ℝ)*x 1 + (91450483/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335754211/1000000000 : ℝ)^85 ≤ (13034170786907/50000000000000 : ℝ)^69 := by
    have hnat : (335754211 : ℕ)^85*50000000000000^69 ≤ 13034170786907^69*1000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335754211 1000000000 13034170786907 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613055057/5000000000 : ℝ)^85 ≤ (44960243640363/100000000000000 : ℝ)^69 := by
    have hnat : (2613055057 : ℕ)^85*100000000000000^69 ≤ 44960243640363^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613055057 5000000000 44960243640363 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91450483/250000000 : ℝ)^85 ≤ (28971414776423/100000000000000 : ℝ)^69 := by
    have hnat : (91450483 : ℕ)^85*100000000000000^69 ≤ 28971414776423^69*250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91450483 250000000 28971414776423 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335754211/1000000000 : ℝ), (2613055057/5000000000 : ℝ), (91450483/250000000 : ℝ)] ![(13034170786907/50000000000000 : ℝ), (44960243640363/100000000000000 : ℝ), (28971414776423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335754211/1000000000 : ℝ)|^85 ≤ (13034170786907/50000000000000 : ℝ)^69
        have hw : |(335754211/1000000000 : ℝ)|=(335754211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613055057/5000000000 : ℝ)|^85 ≤ (44960243640363/100000000000000 : ℝ)^69
        have hw : |(2613055057/5000000000 : ℝ)|=(2613055057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(91450483/250000000 : ℝ)|^85 ≤ (28971414776423/100000000000000 : ℝ)^69
        have hw : |(91450483/250000000 : ℝ)|=(91450483/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s0_9 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1196489347/2000000000 : ℝ)*x 0 + (-719723891/2000000000 : ℝ)*x 1 + (-508361139/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1196489347/2000000000 : ℝ)^85 ≤ (10621126864779/20000000000000 : ℝ)^69 := by
    have hnat : (1196489347 : ℕ)^85*20000000000000^69 ≤ 10621126864779^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196489347 2000000000 10621126864779 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (719723891/2000000000 : ℝ)^85 ≤ (56785952647/200000000000 : ℝ)^69 := by
    have hnat : (719723891 : ℕ)^85*200000000000^69 ≤ 56785952647^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719723891 2000000000 56785952647 200000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508361139/2000000000 : ℝ)^85 ≤ (3700277866223/20000000000000 : ℝ)^69 := by
    have hnat : (508361139 : ℕ)^85*20000000000000^69 ≤ 3700277866223^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508361139 2000000000 3700277866223 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1196489347/2000000000 : ℝ), (-719723891/2000000000 : ℝ), (-508361139/2000000000 : ℝ)] ![(10621126864779/20000000000000 : ℝ), (56785952647/200000000000 : ℝ), (3700277866223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1196489347/2000000000 : ℝ)|^85 ≤ (10621126864779/20000000000000 : ℝ)^69
        have hw : |(1196489347/2000000000 : ℝ)|=(1196489347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-719723891/2000000000 : ℝ)|^85 ≤ (56785952647/200000000000 : ℝ)^69
        have hw : |(-719723891/2000000000 : ℝ)|=(719723891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-508361139/2000000000 : ℝ)|^85 ≤ (3700277866223/20000000000000 : ℝ)^69
        have hw : |(-508361139/2000000000 : ℝ)|=(508361139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s0_13 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1928497/10000000000 : ℝ)*x 0 + (-1479590959/10000000000 : ℝ)*x 1 + (1152682283/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1928497/10000000000 : ℝ)^85 ≤ (663377101/25000000000000 : ℝ)^69 := by
    have hnat : (1928497 : ℕ)^85*25000000000000^69 ≤ 663377101^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928497 10000000000 663377101 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1479590959/10000000000 : ℝ)^85 ≤ (1899943766869/20000000000000 : ℝ)^69 := by
    have hnat : (1479590959 : ℕ)^85*20000000000000^69 ≤ 1899943766869^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479590959 10000000000 1899943766869 20000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1152682283/1250000000 : ℝ)^85 ≤ (90497627653289/100000000000000 : ℝ)^69 := by
    have hnat : (1152682283 : ℕ)^85*100000000000000^69 ≤ 90497627653289^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152682283 1250000000 90497627653289 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1928497/10000000000 : ℝ), (-1479590959/10000000000 : ℝ), (1152682283/1250000000 : ℝ)] ![(663377101/25000000000000 : ℝ), (1899943766869/20000000000000 : ℝ), (90497627653289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1928497/10000000000 : ℝ)|^85 ≤ (663377101/25000000000000 : ℝ)^69
        have hw : |(-1928497/10000000000 : ℝ)|=(1928497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1479590959/10000000000 : ℝ)|^85 ≤ (1899943766869/20000000000000 : ℝ)^69
        have hw : |(-1479590959/10000000000 : ℝ)|=(1479590959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1152682283/1250000000 : ℝ)|^85 ≤ (90497627653289/100000000000000 : ℝ)^69
        have hw : |(1152682283/1250000000 : ℝ)|=(1152682283/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s0_14 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-806714633/2500000000 : ℝ)*x 0 + (-631998433/2000000000 : ℝ)*x 1 + (1157536211/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (806714633/2500000000 : ℝ)^85 ≤ (775753678433/3125000000000 : ℝ)^69 := by
    have hnat : (806714633 : ℕ)^85*3125000000000^69 ≤ 775753678433^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806714633 2500000000 775753678433 3125000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (631998433/2000000000 : ℝ)^85 ≤ (3023995771791/12500000000000 : ℝ)^69 := by
    have hnat : (631998433 : ℕ)^85*12500000000000^69 ≤ 3023995771791^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631998433 2000000000 3023995771791 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1157536211/2000000000 : ℝ)^85 ≤ (407871328829/800000000000 : ℝ)^69 := by
    have hnat : (1157536211 : ℕ)^85*800000000000^69 ≤ 407871328829^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157536211 2000000000 407871328829 800000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-806714633/2500000000 : ℝ), (-631998433/2000000000 : ℝ), (1157536211/2000000000 : ℝ)] ![(775753678433/3125000000000 : ℝ), (3023995771791/12500000000000 : ℝ), (407871328829/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-806714633/2500000000 : ℝ)|^85 ≤ (775753678433/3125000000000 : ℝ)^69
        have hw : |(-806714633/2500000000 : ℝ)|=(806714633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-631998433/2000000000 : ℝ)|^85 ≤ (3023995771791/12500000000000 : ℝ)^69
        have hw : |(-631998433/2000000000 : ℝ)|=(631998433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1157536211/2000000000 : ℝ)|^85 ≤ (407871328829/800000000000 : ℝ)^69
        have hw : |(1157536211/2000000000 : ℝ)|=(1157536211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s0_15 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4876719531/10000000000 : ℝ)*x 0 + (291919699/625000000 : ℝ)*x 1 + (531949011/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4876719531/10000000000 : ℝ)^85 ≤ (41286644057507/100000000000000 : ℝ)^69 := by
    have hnat : (4876719531 : ℕ)^85*100000000000000^69 ≤ 41286644057507^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4876719531 10000000000 41286644057507 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (291919699/625000000 : ℝ)^85 ≤ (39148818791067/100000000000000 : ℝ)^69 := by
    have hnat : (291919699 : ℕ)^85*100000000000000^69 ≤ 39148818791067^69*625000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291919699 625000000 39148818791067 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531949011/2000000000 : ℝ)^85 ≤ (19564537136219/100000000000000 : ℝ)^69 := by
    have hnat : (531949011 : ℕ)^85*100000000000000^69 ≤ 19564537136219^69*2000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531949011 2000000000 19564537136219 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4876719531/10000000000 : ℝ), (291919699/625000000 : ℝ), (531949011/2000000000 : ℝ)] ![(41286644057507/100000000000000 : ℝ), (39148818791067/100000000000000 : ℝ), (19564537136219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4876719531/10000000000 : ℝ)|^85 ≤ (41286644057507/100000000000000 : ℝ)^69
        have hw : |(4876719531/10000000000 : ℝ)|=(4876719531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(291919699/625000000 : ℝ)|^85 ≤ (39148818791067/100000000000000 : ℝ)^69
        have hw : |(291919699/625000000 : ℝ)|=(291919699/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531949011/2000000000 : ℝ)|^85 ≤ (19564537136219/100000000000000 : ℝ)^69
        have hw : |(531949011/2000000000 : ℝ)|=(531949011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s0_16 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7389564183/10000000000 : ℝ)*x 0 + (-744314943/2500000000 : ℝ)*x 1 + (-342163039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7389564183/10000000000 : ℝ)^85 ≤ (8611199259871/12500000000000 : ℝ)^69 := by
    have hnat : (7389564183 : ℕ)^85*12500000000000^69 ≤ 8611199259871^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7389564183 10000000000 8611199259871 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744314943/2500000000 : ℝ)^85 ≤ (5620089425669/25000000000000 : ℝ)^69 := by
    have hnat : (744314943 : ℕ)^85*25000000000000^69 ≤ 5620089425669^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744314943 2500000000 5620089425669 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342163039/2500000000 : ℝ)^85 ≤ (4315024104181/50000000000000 : ℝ)^69 := by
    have hnat : (342163039 : ℕ)^85*50000000000000^69 ≤ 4315024104181^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342163039 2500000000 4315024104181 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7389564183/10000000000 : ℝ), (-744314943/2500000000 : ℝ), (-342163039/2500000000 : ℝ)] ![(8611199259871/12500000000000 : ℝ), (5620089425669/25000000000000 : ℝ), (4315024104181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7389564183/10000000000 : ℝ)|^85 ≤ (8611199259871/12500000000000 : ℝ)^69
        have hw : |(7389564183/10000000000 : ℝ)|=(7389564183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-744314943/2500000000 : ℝ)|^85 ≤ (5620089425669/25000000000000 : ℝ)^69
        have hw : |(-744314943/2500000000 : ℝ)|=(744314943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-342163039/2500000000 : ℝ)|^85 ≤ (4315024104181/50000000000000 : ℝ)^69
        have hw : |(-342163039/2500000000 : ℝ)|=(342163039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s0_20 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-19373/5000000000 : ℝ)*x 0 + (-44476057/250000000 : ℝ)*x 1 + (9020878713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19373/5000000000 : ℝ)^85 ≤ (21543833/100000000000000 : ℝ)^69 := by
    have hnat : (19373 : ℕ)^85*100000000000000^69 ≤ 21543833^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19373 5000000000 21543833 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44476057/250000000 : ℝ)^85 ≤ (11921102411451/100000000000000 : ℝ)^69 := by
    have hnat : (44476057 : ℕ)^85*100000000000000^69 ≤ 11921102411451^69*250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44476057 250000000 11921102411451 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9020878713/10000000000 : ℝ)^85 ≤ (11009859503721/12500000000000 : ℝ)^69 := by
    have hnat : (9020878713 : ℕ)^85*12500000000000^69 ≤ 11009859503721^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9020878713 10000000000 11009859503721 12500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19373/5000000000 : ℝ), (-44476057/250000000 : ℝ), (9020878713/10000000000 : ℝ)] ![(21543833/100000000000000 : ℝ), (11921102411451/100000000000000 : ℝ), (11009859503721/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19373/5000000000 : ℝ)|^85 ≤ (21543833/100000000000000 : ℝ)^69
        have hw : |(-19373/5000000000 : ℝ)|=(19373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44476057/250000000 : ℝ)|^85 ≤ (11921102411451/100000000000000 : ℝ)^69
        have hw : |(-44476057/250000000 : ℝ)|=(44476057/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9020878713/10000000000 : ℝ)|^85 ≤ (11009859503721/12500000000000 : ℝ)^69
        have hw : |(9020878713/10000000000 : ℝ)|=(9020878713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s0_21 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3277931289/10000000000 : ℝ)*x 0 + (-4255986029/10000000000 : ℝ)*x 1 + (4731681617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3277931289/10000000000 : ℝ)^85 ≤ (12654505435039/50000000000000 : ℝ)^69 := by
    have hnat : (3277931289 : ℕ)^85*50000000000000^69 ≤ 12654505435039^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3277931289 10000000000 12654505435039 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4255986029/10000000000 : ℝ)^85 ≤ (872793014587/2500000000000 : ℝ)^69 := by
    have hnat : (4255986029 : ℕ)^85*2500000000000^69 ≤ 872793014587^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255986029 10000000000 872793014587 2500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4731681617/10000000000 : ℝ)^85 ≤ (39779268537603/100000000000000 : ℝ)^69 := by
    have hnat : (4731681617 : ℕ)^85*100000000000000^69 ≤ 39779268537603^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4731681617 10000000000 39779268537603 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3277931289/10000000000 : ℝ), (-4255986029/10000000000 : ℝ), (4731681617/10000000000 : ℝ)] ![(12654505435039/50000000000000 : ℝ), (872793014587/2500000000000 : ℝ), (39779268537603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3277931289/10000000000 : ℝ)|^85 ≤ (12654505435039/50000000000000 : ℝ)^69
        have hw : |(-3277931289/10000000000 : ℝ)|=(3277931289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4255986029/10000000000 : ℝ)|^85 ≤ (872793014587/2500000000000 : ℝ)^69
        have hw : |(-4255986029/10000000000 : ℝ)|=(4255986029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4731681617/10000000000 : ℝ)|^85 ≤ (39779268537603/100000000000000 : ℝ)^69
        have hw : |(4731681617/10000000000 : ℝ)|=(4731681617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s0_22 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (739638961/2500000000 : ℝ)*x 0 + (1350337339/2500000000 : ℝ)*x 1 + (1925668489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (739638961/2500000000 : ℝ)^85 ≤ (2230650870607/10000000000000 : ℝ)^69 := by
    have hnat : (739638961 : ℕ)^85*10000000000000^69 ≤ 2230650870607^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739638961 2500000000 2230650870607 10000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350337339/2500000000 : ℝ)^85 ≤ (46824571150833/100000000000000 : ℝ)^69 := by
    have hnat : (1350337339 : ℕ)^85*100000000000000^69 ≤ 46824571150833^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350337339 2500000000 46824571150833 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1925668489/5000000000 : ℝ)^85 ≤ (15434460063777/50000000000000 : ℝ)^69 := by
    have hnat : (1925668489 : ℕ)^85*50000000000000^69 ≤ 15434460063777^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925668489 5000000000 15434460063777 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(739638961/2500000000 : ℝ), (1350337339/2500000000 : ℝ), (1925668489/5000000000 : ℝ)] ![(2230650870607/10000000000000 : ℝ), (46824571150833/100000000000000 : ℝ), (15434460063777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(739638961/2500000000 : ℝ)|^85 ≤ (2230650870607/10000000000000 : ℝ)^69
        have hw : |(739638961/2500000000 : ℝ)|=(739638961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350337339/2500000000 : ℝ)|^85 ≤ (46824571150833/100000000000000 : ℝ)^69
        have hw : |(1350337339/2500000000 : ℝ)|=(1350337339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1925668489/5000000000 : ℝ)|^85 ≤ (15434460063777/50000000000000 : ℝ)^69
        have hw : |(1925668489/5000000000 : ℝ)|=(1925668489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s0_23 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (879462791/1250000000 : ℝ)*x 0 + (-2952893797/10000000000 : ℝ)*x 1 + (-1896441273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (879462791/1250000000 : ℝ)^85 ≤ (16212145725509/25000000000000 : ℝ)^69 := by
    have hnat : (879462791 : ℕ)^85*25000000000000^69 ≤ 16212145725509^69*1250000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879462791 1250000000 16212145725509 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2952893797/10000000000 : ℝ)^85 ≤ (695435354801/3125000000000 : ℝ)^69 := by
    have hnat : (2952893797 : ℕ)^85*3125000000000^69 ≤ 695435354801^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2952893797 10000000000 695435354801 3125000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1896441273/10000000000 : ℝ)^85 ≤ (12897485731603/100000000000000 : ℝ)^69 := by
    have hnat : (1896441273 : ℕ)^85*100000000000000^69 ≤ 12897485731603^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896441273 10000000000 12897485731603 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(879462791/1250000000 : ℝ), (-2952893797/10000000000 : ℝ), (-1896441273/10000000000 : ℝ)] ![(16212145725509/25000000000000 : ℝ), (695435354801/3125000000000 : ℝ), (12897485731603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(879462791/1250000000 : ℝ)|^85 ≤ (16212145725509/25000000000000 : ℝ)^69
        have hw : |(879462791/1250000000 : ℝ)|=(879462791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2952893797/10000000000 : ℝ)|^85 ≤ (695435354801/3125000000000 : ℝ)^69
        have hw : |(-2952893797/10000000000 : ℝ)|=(2952893797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1896441273/10000000000 : ℝ)|^85 ≤ (12897485731603/100000000000000 : ℝ)^69
        have hw : |(-1896441273/10000000000 : ℝ)|=(1896441273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s1_0 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-856303159/2500000000 : ℝ)*x 0 + (-941842281/2500000000 : ℝ)*x 1 + (5063289029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (856303159/2500000000 : ℝ)^85 ≤ (26717080283233/100000000000000 : ℝ)^69 := by
    have hnat : (856303159 : ℕ)^85*100000000000000^69 ≤ 26717080283233^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856303159 2500000000 26717080283233 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (941842281/2500000000 : ℝ)^85 ≤ (15020977302097/50000000000000 : ℝ)^69 := by
    have hnat : (941842281 : ℕ)^85*50000000000000^69 ≤ 15020977302097^69*2500000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941842281 2500000000 15020977302097 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5063289029/10000000000 : ℝ)^85 ≤ (864819302129/2000000000000 : ℝ)^69 := by
    have hnat : (5063289029 : ℕ)^85*2000000000000^69 ≤ 864819302129^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5063289029 10000000000 864819302129 2000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-856303159/2500000000 : ℝ), (-941842281/2500000000 : ℝ), (5063289029/10000000000 : ℝ)] ![(26717080283233/100000000000000 : ℝ), (15020977302097/50000000000000 : ℝ), (864819302129/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-856303159/2500000000 : ℝ)|^85 ≤ (26717080283233/100000000000000 : ℝ)^69
        have hw : |(-856303159/2500000000 : ℝ)|=(856303159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-941842281/2500000000 : ℝ)|^85 ≤ (15020977302097/50000000000000 : ℝ)^69
        have hw : |(-941842281/2500000000 : ℝ)|=(941842281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5063289029/10000000000 : ℝ)|^85 ≤ (864819302129/2000000000000 : ℝ)^69
        have hw : |(5063289029/10000000000 : ℝ)|=(5063289029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s1_1 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4166363039/10000000000 : ℝ)*x 0 + (2296669607/5000000000 : ℝ)*x 1 + (3520982539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166363039/10000000000 : ℝ)^85 ≤ (272066351373/800000000000 : ℝ)^69 := by
    have hnat : (4166363039 : ℕ)^85*800000000000^69 ≤ 272066351373^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166363039 10000000000 272066351373 800000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2296669607/5000000000 : ℝ)^85 ≤ (9587856323931/25000000000000 : ℝ)^69 := by
    have hnat : (2296669607 : ℕ)^85*25000000000000^69 ≤ 9587856323931^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296669607 5000000000 9587856323931 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3520982539/10000000000 : ℝ)^85 ≤ (13820140382783/50000000000000 : ℝ)^69 := by
    have hnat : (3520982539 : ℕ)^85*50000000000000^69 ≤ 13820140382783^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3520982539 10000000000 13820140382783 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166363039/10000000000 : ℝ), (2296669607/5000000000 : ℝ), (3520982539/10000000000 : ℝ)] ![(272066351373/800000000000 : ℝ), (9587856323931/25000000000000 : ℝ), (13820140382783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166363039/10000000000 : ℝ)|^85 ≤ (272066351373/800000000000 : ℝ)^69
        have hw : |(4166363039/10000000000 : ℝ)|=(4166363039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2296669607/5000000000 : ℝ)|^85 ≤ (9587856323931/25000000000000 : ℝ)^69
        have hw : |(2296669607/5000000000 : ℝ)|=(2296669607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3520982539/10000000000 : ℝ)|^85 ≤ (13820140382783/50000000000000 : ℝ)^69
        have hw : |(3520982539/10000000000 : ℝ)|=(3520982539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s1_2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4970660219/10000000000 : ℝ)*x 0 + (-4140302037/10000000000 : ℝ)*x 1 + (-3138031037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4970660219/10000000000 : ℝ)^85 ≤ (1056713728887/2500000000000 : ℝ)^69 := by
    have hnat : (4970660219 : ℕ)^85*2500000000000^69 ≤ 1056713728887^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4970660219 10000000000 1056713728887 2500000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4140302037/10000000000 : ℝ)^85 ≤ (16873215774979/50000000000000 : ℝ)^69 := by
    have hnat : (4140302037 : ℕ)^85*50000000000000^69 ≤ 16873215774979^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140302037 10000000000 16873215774979 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3138031037/10000000000 : ℝ)^85 ≤ (11992509635399/50000000000000 : ℝ)^69 := by
    have hnat : (3138031037 : ℕ)^85*50000000000000^69 ≤ 11992509635399^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3138031037 10000000000 11992509635399 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4970660219/10000000000 : ℝ), (-4140302037/10000000000 : ℝ), (-3138031037/10000000000 : ℝ)] ![(1056713728887/2500000000000 : ℝ), (16873215774979/50000000000000 : ℝ), (11992509635399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4970660219/10000000000 : ℝ)|^85 ≤ (1056713728887/2500000000000 : ℝ)^69
        have hw : |(4970660219/10000000000 : ℝ)|=(4970660219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4140302037/10000000000 : ℝ)|^85 ≤ (16873215774979/50000000000000 : ℝ)^69
        have hw : |(-4140302037/10000000000 : ℝ)|=(4140302037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3138031037/10000000000 : ℝ)|^85 ≤ (11992509635399/50000000000000 : ℝ)^69
        have hw : |(-3138031037/10000000000 : ℝ)|=(3138031037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c324071_s1_6 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3079660377/10000000000 : ℝ)*x 0 + (-198694509/625000000 : ℝ)*x 1 + (2949333947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3079660377/10000000000 : ℝ)^85 ≤ (23436609556857/100000000000000 : ℝ)^69 := by
    have hnat : (3079660377 : ℕ)^85*100000000000000^69 ≤ 23436609556857^69*10000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3079660377 10000000000 23436609556857 100000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198694509/625000000 : ℝ)^85 ≤ (12186205928849/50000000000000 : ℝ)^69 := by
    have hnat : (198694509 : ℕ)^85*50000000000000^69 ≤ 12186205928849^69*625000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198694509 625000000 12186205928849 50000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2949333947/5000000000 : ℝ)^85 ≤ (13047744641309/25000000000000 : ℝ)^69 := by
    have hnat : (2949333947 : ℕ)^85*25000000000000^69 ≤ 13047744641309^69*5000000000^85 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2949333947 5000000000 13047744641309 25000000000000 85 69 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (85/16 : ℝ)) 85 69 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3079660377/10000000000 : ℝ), (-198694509/625000000 : ℝ), (2949333947/5000000000 : ℝ)] ![(23436609556857/100000000000000 : ℝ), (12186205928849/50000000000000 : ℝ), (13047744641309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3079660377/10000000000 : ℝ)|^85 ≤ (23436609556857/100000000000000 : ℝ)^69
        have hw : |(3079660377/10000000000 : ℝ)|=(3079660377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-198694509/625000000 : ℝ)|^85 ≤ (12186205928849/50000000000000 : ℝ)^69
        have hw : |(-198694509/625000000 : ℝ)|=(198694509/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2949333947/5000000000 : ℝ)|^85 ≤ (13047744641309/25000000000000 : ℝ)^69
        have hw : |(2949333947/5000000000 : ℝ)|=(2949333947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c324071 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81117/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (83049/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(141140309994013/1000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (141140309994013/1000000000000000 : ℝ)) (beta := (916245292417331/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(141140309994013/1000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(916245292417331/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((3533431551/10000000000 : ℝ)*X 1 0+(2524956969/5000000000 : ℝ)*X 1 1+(1837592627/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1250002187/2000000000 : ℝ)*X 2 0+(-715170913/2000000000 : ℝ)*X 2 1+(-446803981/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-3758479401/10000000000 : ℝ)*X 0 0+(-4699654303/10000000000 : ℝ)*X 0 1+(1911912901/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((335754211/1000000000 : ℝ)*X 1 0+(2613055057/5000000000 : ℝ)*X 1 1+(91450483/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1196489347/2000000000 : ℝ)*X 2 0+(-719723891/2000000000 : ℝ)*X 2 1+(-508361139/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-1928497/10000000000 : ℝ)*X 0 0+(-1479590959/10000000000 : ℝ)*X 0 1+(1152682283/1250000000 : ℝ)*X 0 2+(-1928497/10000000000 : ℝ)*X 1 0+(-1479590959/10000000000 : ℝ)*X 1 1+(1152682283/1250000000 : ℝ)*X 1 2+(-1928497/10000000000 : ℝ)*X 2 0+(-1479590959/10000000000 : ℝ)*X 2 1+(1152682283/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-806714633/2500000000 : ℝ)*X 0 0+(-631998433/2000000000 : ℝ)*X 0 1+(1157536211/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4876719531/10000000000 : ℝ)*X 1 0+(291919699/625000000 : ℝ)*X 1 1+(531949011/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7389564183/10000000000 : ℝ)*X 2 0+(-744314943/2500000000 : ℝ)*X 2 1+(-342163039/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-19373/5000000000 : ℝ)*X 0 0+(-44476057/250000000 : ℝ)*X 0 1+(9020878713/10000000000 : ℝ)*X 0 2+(-19373/5000000000 : ℝ)*X 1 0+(-44476057/250000000 : ℝ)*X 1 1+(9020878713/10000000000 : ℝ)*X 1 2+(-19373/5000000000 : ℝ)*X 2 0+(-44476057/250000000 : ℝ)*X 2 1+(9020878713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-3277931289/10000000000 : ℝ)*X 0 0+(-4255986029/10000000000 : ℝ)*X 0 1+(4731681617/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((739638961/2500000000 : ℝ)*X 1 0+(1350337339/2500000000 : ℝ)*X 1 1+(1925668489/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((879462791/1250000000 : ℝ)*X 2 0+(-2952893797/10000000000 : ℝ)*X 2 1+(-1896441273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((14963/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14963/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5998161606362790389511/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (260502708753/1000000000000 : ℝ)*(base1) + (748063228707/1000000000000 : ℝ)*(base7) + (228127/200000000000 : ℝ)*(base22) + (562537/250000000000 : ℝ)*(base54) + (589329434693/500000000000 : ℝ)*(base60) + (187618348143/50000000000 : ℝ)*(major_s0_0) + (187618348143/50000000000 : ℝ)*(major_s0_1) + (469045589089/125000000000 : ℝ)*(major_s0_2) + (5458629069663/1000000000000 : ℝ)*(sp_s0_7) + (1299534797529/250000000000 : ℝ)*(sp_s0_8) + (5198135799333/1000000000000 : ℝ)*(sp_s0_9) + (1189908800737/500000000000 : ℝ)*(sp_s0_13) + (80558607/500000000000 : ℝ)*(sp_s0_20) + (6414603/500000000000 : ℝ)*(sp_s0_21) + (1892420448881/1000000000000 : ℝ)*(f.failure) + (1299534797529/250000000000 : ℝ)*(f.sum) + (55613633587039/500000000000000000000000000 : ℝ)*base63 + (679939434476459/1250000000000000000000000000 : ℝ)*base64 + (2187208062141/50000000000000000000000000 : ℝ)*base66 + (52493270150843/125000000000000000000000000 : ℝ)*base69 + (15705712956873/156250000000000000000000000 : ℝ)*base70 + (91723787033667/500000000000000000000000000 : ℝ)*base72 + (73828081516333/500000000000000000000000000 : ℝ)*base74 + (4908804672859/50000000000000000000000000 : ℝ)*base77 + (341108862605077/500000000000000000000000000 : ℝ)*base78 + (19949/25000000000000000 : ℝ)*base86 + (19949/25000000000000000 : ℝ)*base88 + (19949/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-6259/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-6259/10000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (51202045799665077987093/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12712840419/15625000000 : ℝ)*(base1) + (661556656851/500000000000 : ℝ)*(base7) + (392068057047/1000000000000 : ℝ)*(base40) + (356629886903/500000000000 : ℝ)*(base60) + (2749833248629/1000000000000 : ℝ)*(major_s0_0) + (2749833248629/1000000000000 : ℝ)*(major_s0_1) + (2749833248629/1000000000000 : ℝ)*(major_s0_2) + (1996503/50000000000 : ℝ)*(sp_s0_1) + (30278999/100000000000 : ℝ)*(sp_s0_13) + (262119653251/62500000000 : ℝ)*(sp_s0_14) + (3380252735141/1000000000000 : ℝ)*(sp_s0_15) + (422534872379/125000000000 : ℝ)*(sp_s0_16) + (1896004238211/1000000000000 : ℝ)*(sp_s0_20) + (1710771/125000000000 : ℝ)*(sp_s0_23) + (346703875329/250000000000 : ℝ)*(f.failure) + (8450731663/2500000000 : ℝ)*(f.sum) + (6650928508170969/10000000000000000000000000000 : ℝ)*base62 + (91351978410801/10000000000000000000000000000 : ℝ)*base65 + (876599662158177/1000000000000000000000000000 : ℝ)*base67 + (572982679958177/1000000000000000000000000000 : ℝ)*base68 + (4466526581007429/10000000000000000000000000000 : ℝ)*base70 + (8841471353589199/10000000000000000000000000000 : ℝ)*base73 + (4089494324410801/10000000000000000000000000000 : ℝ)*base75 + (855390460541823/1000000000000000000000000000 : ℝ)*base76 + (8943122509170969/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (2609/6250000000000000 : ℝ)*base87 + (2609/6250000000000000 : ℝ)*base89 + (2609/6250000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(238/625 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(238/625 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (86387382502084237083/3906250000000000000000000 : ℝ) := by norm_num
    linear_combination (1424822757509/500000000000 : ℝ)*(base1) + (602487699213/500000000000 : ℝ)*(base7) + (155754660151/100000000000 : ℝ)*(base40) + (555165192713/1000000000000 : ℝ)*(base60) + (101909927937/31250000000 : ℝ)*(major_s0_0) + (101909927937/31250000000 : ℝ)*(major_s0_1) + (101909927937/31250000000 : ℝ)*(major_s0_2) + (92452343/1000000000000 : ℝ)*(sp_s0_2) + (13337227/1000000000000 : ℝ)*(sp_s0_7) + (22975691/250000000000 : ℝ)*(sp_s0_8) + (37199511/200000000000 : ℝ)*(sp_s0_16) + (3530021699171/500000000000 : ℝ)*(sp_s0_21) + (1052579829447/250000000000 : ℝ)*(sp_s0_22) + (2105066385327/500000000000 : ℝ)*(sp_s0_23) + (102791882287/62500000000 : ℝ)*(f.failure) + (526301402569/125000000000 : ℝ)*(f.sum) + (132799433506707/312500000000000000000000000 : ℝ)*base62 + (256494686782397/312500000000000000000000000 : ℝ)*base64 + (27645074978681/31250000000000000000000000 : ℝ)*base67 + (10744440083819/31250000000000000000000000 : ℝ)*base69 + (122046961285663/312500000000000000000000000 : ℝ)*base71 + (24102079126147/312500000000000000000000000 : ℝ)*base73 + (112185704436353/312500000000000000000000000 : ℝ)*base75 + (311594615903/15625000000000000000000000 : ℝ)*base77 + (74867678930793/312500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1123/1562500000000000 : ℝ)*base86 + (1123/1562500000000000 : ℝ)*base88 + (1123/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (14963/50000 : ℝ) ^ (21/4 : ℝ) ≤ (177523366814976747/100000000000000000000 : ℝ) := by
    have hpowers : (14963/50000 : ℝ)^21 ≤ (177523366814976747/100000000000000000000 : ℝ)^4 := by
      have hnat : (14963 : ℕ)^21*100000000000000000000^4 ≤ 177523366814976747^4*50000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14963 50000 177523366814976747 100000000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14963/50000 : ℝ)) (X := (177523366814976747/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100177523366814976747/100000000000000000000 : ℝ) ≤ (10003378970368689/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (100177523366814976747/100000000000000000000 : ℝ)^4 ≤ (10003378970368689/10000000000000000 : ℝ)^21 := by
      have hnat : (100177523366814976747 : ℕ)^4*10000000000000000^21 ≤ 10003378970368689^21*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100177523366814976747 100000000000000000000 10003378970368689 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003378970368689/10000000000000000 : ℝ)) (X := (100177523366814976747/100000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50177523366814976747/50000000000000000000 : ℝ) ≤ (1000675309691629/1000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (50177523366814976747/50000000000000000000 : ℝ)^4 ≤ (1000675309691629/1000000000000000 : ℝ)^21 := by
      have hnat : (50177523366814976747 : ℕ)^4*1000000000000000^21 ≤ 1000675309691629^21*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50177523366814976747 50000000000000000000 1000675309691629 1000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000675309691629/1000000000000000 : ℝ)) (X := (50177523366814976747/50000000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3378970368689/2992600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3374126547601/2992600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (14963/50000 : ℝ)) (alpha := (3378970368689/2992600000000000 : ℝ)) (beta := (3374126547601/2992600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (14963/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3378970368689/2992600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3374126547601/2992600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (6259/10000 : ℝ) ^ (21/4 : ℝ) ≤ (533987404290039821/6250000000000000000 : ℝ) := by
    have hpowers : (6259/10000 : ℝ)^21 ≤ (533987404290039821/6250000000000000000 : ℝ)^4 := by
      have hnat : (6259 : ℕ)^21*6250000000000000000^4 ≤ 533987404290039821^4*10000^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6259 10000 533987404290039821 6250000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6259/10000 : ℝ)) (X := (533987404290039821/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (6783987404290039821/6250000000000000000 : ℝ) ≤ (2539346213160363/2500000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (6783987404290039821/6250000000000000000 : ℝ)^4 ≤ (2539346213160363/2500000000000000 : ℝ)^21 := by
      have hnat : (6783987404290039821 : ℕ)^4*2500000000000000^21 ≤ 2539346213160363^21*6250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6783987404290039821 6250000000000000000 2539346213160363 2500000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2539346213160363/2500000000000000 : ℝ)) (X := (6783987404290039821/6250000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (3658987404290039821/3125000000000000000 : ℝ) ≤ (10305040284526949/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3658987404290039821/3125000000000000000 : ℝ)^4 ≤ (10305040284526949/10000000000000000 : ℝ)^21 := by
      have hnat : (3658987404290039821 : ℕ)^4*10000000000000000^21 ≤ 10305040284526949^21*3125000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3658987404290039821 3125000000000000000 10305040284526949 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10305040284526949/10000000000000000 : ℝ)) (X := (3658987404290039821/3125000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(39346213160363/1564750000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(147655431885497/6259000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (6259/10000 : ℝ)) (alpha := (39346213160363/1564750000000000 : ℝ)) (beta := (147655431885497/6259000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (6259/10000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(39346213160363/1564750000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(147655431885497/6259000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (238/625 : ℝ) ^ (21/4 : ℝ) ≤ (39313250244114533/6250000000000000000 : ℝ) := by
    have hpowers : (238/625 : ℝ)^21 ≤ (39313250244114533/6250000000000000000 : ℝ)^4 := by
      have hnat : (238 : ℕ)^21*6250000000000000000^4 ≤ 39313250244114533^4*625^21 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        238 625 39313250244114533 6250000000000000000 21 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (238/625 : ℝ)) (X := (39313250244114533/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (6289313250244114533/6250000000000000000 : ℝ) ≤ (10011950792153193/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (6289313250244114533/6250000000000000000 : ℝ)^4 ≤ (10011950792153193/10000000000000000 : ℝ)^21 := by
      have hnat : (6289313250244114533 : ℕ)^4*10000000000000000^21 ≤ 10011950792153193^21*6250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6289313250244114533 6250000000000000000 10011950792153193 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011950792153193/10000000000000000 : ℝ)) (X := (6289313250244114533/6250000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (3164313250244114533/3125000000000000000 : ℝ) ≤ (10023841263426429/10000000000000000 : ℝ) ^ (21/4 : ℝ) := by
    have hpowers : (3164313250244114533/3125000000000000000 : ℝ)^4 ≤ (10023841263426429/10000000000000000 : ℝ)^21 := by
      have hnat : (3164313250244114533 : ℕ)^4*10000000000000000^21 ≤ 10023841263426429^21*3125000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3164313250244114533 3125000000000000000 10023841263426429 10000000000000000 4 21 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10023841263426429/10000000000000000 : ℝ)) (X := (3164313250244114533/3125000000000000000 : ℝ)) (by norm_num) 21 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(11950792153193/3808000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(2972617818309/952000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (21/4 : ℝ)) (rho := (238/625 : ℝ)) (alpha := (11950792153193/3808000000000000 : ℝ)) (beta := (2972617818309/952000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (238/625 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(11950792153193/3808000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(2972617818309/952000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-856303159/2500000000 : ℝ)*X 0 0+(-941842281/2500000000 : ℝ)*X 0 1+(5063289029/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4166363039/10000000000 : ℝ)*X 1 0+(2296669607/5000000000 : ℝ)*X 1 1+(3520982539/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4970660219/10000000000 : ℝ)*X 2 0+(-4140302037/10000000000 : ℝ)*X 2 1+(-3138031037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3079660377/10000000000 : ℝ)*X 0 0+(-198694509/625000000 : ℝ)*X 0 1+(2949333947/5000000000 : ℝ)*X 0 2+(3079660377/10000000000 : ℝ)*X 1 0+(-198694509/625000000 : ℝ)*X 1 1+(2949333947/5000000000 : ℝ)*X 1 2+(3079660377/10000000000 : ℝ)*X 2 0+(-198694509/625000000 : ℝ)*X 2 1+(2949333947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c324071_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-111213/12500 : ℝ) < ((-49571/25000 : ℝ)*P 0+(-49571/25000 : ℝ)*P 1+(-49571/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-111213/12500 : ℝ) < (-2426327813273570313136044050384631/278618915575000000000000000000000 : ℝ) := by norm_num
    linear_combination (64499322811/200000000000 : ℝ)*(base1) + (1129/50000000000 : ℝ)*(base3) + (11923/500000000000 : ℝ)*(base22) + (563366879059/1000000000000 : ℝ)*(base40) + (26379/250000000000 : ℝ)*(base43) + (284530186459/1000000000000 : ℝ)*(base49) + (32577/500000000000 : ℝ)*(base50) + (279277929293/500000000000 : ℝ)*(base60) + (49571/25000 : ℝ)*(major_s1_0) + (495709973621/250000000000 : ℝ)*(major_s1_1) + (49571/25000 : ℝ)*(major_s1_2) + (403162489609/125000000000 : ℝ)*(sp_s1_0) + (2902803430913/1000000000000 : ℝ)*(sp_s1_1) + (2902803278971/1000000000000 : ℝ)*(sp_s1_2) + (135500672673/200000000000 : ℝ)*(sp_s1_6) + (2902803408333/1000000000000 : ℝ)*(f.sum) + (17292560658598609/23275656250000000000000000000 : ℝ)*base63 + (5779620379/37187500000000000000000 : ℝ)*base64 + (302697960032821/782375000000000000000000000 : ℝ)*base67 + (57984413/4648437500000000000000 : ℝ)*base68 + (373180940074867/8902985000000000000000000000 : ℝ)*base70 + (15290665392571/149630000000000000000000000 : ℝ)*base72 + (967663189355713/1564750000000000000000000000 : ℝ)*base75 + (10115425129019/149630000000000000000000000 : ℝ)*base76 + (9204294906712817621/23413354250000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p024_b036 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=70 ∨ c=71 := by omega
  rcases hc with rfl|rfl
  · exact collision_c324070 p hpa (by linarith only [hpb]) X hX
  · exact collision_c324071 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 70 ≤ c.val) (hhi : c.val < 72)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024_b036 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

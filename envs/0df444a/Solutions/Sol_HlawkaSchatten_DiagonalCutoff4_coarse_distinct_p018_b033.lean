-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p018_b033
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:20:46.964062+00:00
-- url     : https://prove2.me/submissions/c2b8a50b-d842-4524-9aba-66de1be38782

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
theorem collision_support_c318075_s0_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1147839/100000000 : ℝ)*x 0 + (-6970827659/10000000000 : ℝ)*x 1 + (2215109299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1147839/100000000 : ℝ)^79 ≤ (369107046107/100000000000000 : ℝ)^63 := by
    have hnat : (1147839 : ℕ)^79*100000000000000^63 ≤ 369107046107^63*100000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147839 100000000 369107046107 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6970827659/10000000000 : ℝ)^79 ≤ (63603870496761/100000000000000 : ℝ)^63 := by
    have hnat : (6970827659 : ℕ)^79*100000000000000^63 ≤ 63603870496761^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6970827659 10000000000 63603870496761 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2215109299/5000000000 : ℝ)^79 ≤ (7205404489191/20000000000000 : ℝ)^63 := by
    have hnat : (2215109299 : ℕ)^79*20000000000000^63 ≤ 7205404489191^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215109299 5000000000 7205404489191 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1147839/100000000 : ℝ), (-6970827659/10000000000 : ℝ), (2215109299/5000000000 : ℝ)] ![(369107046107/100000000000000 : ℝ), (63603870496761/100000000000000 : ℝ), (7205404489191/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1147839/100000000 : ℝ)|^79 ≤ (369107046107/100000000000000 : ℝ)^63
        have hw : |(-1147839/100000000 : ℝ)|=(1147839/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6970827659/10000000000 : ℝ)|^79 ≤ (63603870496761/100000000000000 : ℝ)^63
        have hw : |(-6970827659/10000000000 : ℝ)|=(6970827659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2215109299/5000000000 : ℝ)|^79 ≤ (7205404489191/20000000000000 : ℝ)^63
        have hw : |(2215109299/5000000000 : ℝ)|=(2215109299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s0_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2770571123/5000000000 : ℝ)*x 0 + (-1781651083/5000000000 : ℝ)*x 1 + (-824579043/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2770571123/5000000000 : ℝ)^79 ≤ (47695967271687/100000000000000 : ℝ)^63 := by
    have hnat : (2770571123 : ℕ)^79*100000000000000^63 ≤ 47695967271687^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2770571123 5000000000 47695967271687 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1781651083/5000000000 : ℝ)^79 ≤ (137090530379/500000000000 : ℝ)^63 := by
    have hnat : (1781651083 : ℕ)^79*500000000000^63 ≤ 137090530379^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781651083 5000000000 137090530379 500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (824579043/2500000000 : ℝ)^79 ≤ (12442963322909/50000000000000 : ℝ)^63 := by
    have hnat : (824579043 : ℕ)^79*50000000000000^63 ≤ 12442963322909^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824579043 2500000000 12442963322909 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2770571123/5000000000 : ℝ), (-1781651083/5000000000 : ℝ), (-824579043/2500000000 : ℝ)] ![(47695967271687/100000000000000 : ℝ), (137090530379/500000000000 : ℝ), (12442963322909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2770571123/5000000000 : ℝ)|^79 ≤ (47695967271687/100000000000000 : ℝ)^63
        have hw : |(2770571123/5000000000 : ℝ)|=(2770571123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1781651083/5000000000 : ℝ)|^79 ≤ (137090530379/500000000000 : ℝ)^63
        have hw : |(-1781651083/5000000000 : ℝ)|=(1781651083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-824579043/2500000000 : ℝ)|^79 ≤ (12442963322909/50000000000000 : ℝ)^63
        have hw : |(-824579043/2500000000 : ℝ)|=(824579043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s0_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-191179123/5000000000 : ℝ)*x 0 + (-516553581/625000000 : ℝ)*x 1 + (681258363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (191179123/5000000000 : ℝ)^79 ≤ (1669025448503/100000000000000 : ℝ)^63 := by
    have hnat : (191179123 : ℕ)^79*100000000000000^63 ≤ 1669025448503^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191179123 5000000000 1669025448503 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516553581/625000000 : ℝ)^79 ≤ (787436910217/1000000000000 : ℝ)^63 := by
    have hnat : (516553581 : ℕ)^79*1000000000000^63 ≤ 787436910217^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516553581 625000000 787436910217 1000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681258363/2500000000 : ℝ)^79 ≤ (1224205219601/6250000000000 : ℝ)^63 := by
    have hnat : (681258363 : ℕ)^79*6250000000000^63 ≤ 1224205219601^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681258363 2500000000 1224205219601 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-191179123/5000000000 : ℝ), (-516553581/625000000 : ℝ), (681258363/2500000000 : ℝ)] ![(1669025448503/100000000000000 : ℝ), (787436910217/1000000000000 : ℝ), (1224205219601/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-191179123/5000000000 : ℝ)|^79 ≤ (1669025448503/100000000000000 : ℝ)^63
        have hw : |(-191179123/5000000000 : ℝ)|=(191179123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-516553581/625000000 : ℝ)|^79 ≤ (787436910217/1000000000000 : ℝ)^63
        have hw : |(-516553581/625000000 : ℝ)|=(516553581/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681258363/2500000000 : ℝ)|^79 ≤ (1224205219601/6250000000000 : ℝ)^63
        have hw : |(681258363/2500000000 : ℝ)|=(681258363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s0_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5605627421/10000000000 : ℝ)*x 0 + (1116768669/2500000000 : ℝ)*x 1 + (1113271069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5605627421/10000000000 : ℝ)^79 ≤ (4839302421789/10000000000000 : ℝ)^63 := by
    have hnat : (5605627421 : ℕ)^79*10000000000000^63 ≤ 4839302421789^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5605627421 10000000000 4839302421789 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1116768669/2500000000 : ℝ)^79 ≤ (36403255095909/100000000000000 : ℝ)^63 := by
    have hnat : (1116768669 : ℕ)^79*100000000000000^63 ≤ 36403255095909^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116768669 2500000000 36403255095909 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113271069/5000000000 : ℝ)^79 ≤ (608148827141/4000000000000 : ℝ)^63 := by
    have hnat : (1113271069 : ℕ)^79*4000000000000^63 ≤ 608148827141^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113271069 5000000000 608148827141 4000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5605627421/10000000000 : ℝ), (1116768669/2500000000 : ℝ), (1113271069/5000000000 : ℝ)] ![(4839302421789/10000000000000 : ℝ), (36403255095909/100000000000000 : ℝ), (608148827141/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5605627421/10000000000 : ℝ)|^79 ≤ (4839302421789/10000000000000 : ℝ)^63
        have hw : |(5605627421/10000000000 : ℝ)|=(5605627421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1116768669/2500000000 : ℝ)|^79 ≤ (36403255095909/100000000000000 : ℝ)^63
        have hw : |(1116768669/2500000000 : ℝ)|=(1116768669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1113271069/5000000000 : ℝ)|^79 ≤ (608148827141/4000000000000 : ℝ)^63
        have hw : |(1113271069/5000000000 : ℝ)|=(1113271069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s0_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (266064573/400000000 : ℝ)*x 0 + (-3070518129/10000000000 : ℝ)*x 1 + (-616376197/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266064573/400000000 : ℝ)^79 ≤ (59973052565181/100000000000000 : ℝ)^63 := by
    have hnat : (266064573 : ℕ)^79*100000000000000^63 ≤ 59973052565181^63*400000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266064573 400000000 59973052565181 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3070518129/10000000000 : ℝ)^79 ≤ (4549982263217/20000000000000 : ℝ)^63 := by
    have hnat : (3070518129 : ℕ)^79*20000000000000^63 ≤ 4549982263217^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3070518129 10000000000 4549982263217 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (616376197/2500000000 : ℝ)^79 ≤ (269953689131/1562500000000 : ℝ)^63 := by
    have hnat : (616376197 : ℕ)^79*1562500000000^63 ≤ 269953689131^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      616376197 2500000000 269953689131 1562500000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(266064573/400000000 : ℝ), (-3070518129/10000000000 : ℝ), (-616376197/2500000000 : ℝ)] ![(59973052565181/100000000000000 : ℝ), (4549982263217/20000000000000 : ℝ), (269953689131/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(266064573/400000000 : ℝ)|^79 ≤ (59973052565181/100000000000000 : ℝ)^63
        have hw : |(266064573/400000000 : ℝ)|=(266064573/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3070518129/10000000000 : ℝ)|^79 ≤ (4549982263217/20000000000000 : ℝ)^63
        have hw : |(-3070518129/10000000000 : ℝ)|=(3070518129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-616376197/2500000000 : ℝ)|^79 ≤ (269953689131/1562500000000 : ℝ)^63
        have hw : |(-616376197/2500000000 : ℝ)|=(616376197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s0_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1097335267/10000000000 : ℝ)*x 0 + (-2844039/10000000000 : ℝ)*x 1 + (9497200479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097335267/10000000000 : ℝ)^79 ≤ (6260600537293/100000000000000 : ℝ)^63 := by
    have hnat : (1097335267 : ℕ)^79*100000000000000^63 ≤ 6260600537293^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097335267 10000000000 6260600537293 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2844039/10000000000 : ℝ)^79 ≤ (1787795149/50000000000000 : ℝ)^63 := by
    have hnat : (2844039 : ℕ)^79*50000000000000^63 ≤ 1787795149^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2844039 10000000000 1787795149 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9497200479/10000000000 : ℝ)^79 ≤ (93735823864961/100000000000000 : ℝ)^63 := by
    have hnat : (9497200479 : ℕ)^79*100000000000000^63 ≤ 93735823864961^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9497200479 10000000000 93735823864961 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1097335267/10000000000 : ℝ), (-2844039/10000000000 : ℝ), (9497200479/10000000000 : ℝ)] ![(6260600537293/100000000000000 : ℝ), (1787795149/50000000000000 : ℝ), (93735823864961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1097335267/10000000000 : ℝ)|^79 ≤ (6260600537293/100000000000000 : ℝ)^63
        have hw : |(1097335267/10000000000 : ℝ)|=(1097335267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2844039/10000000000 : ℝ)|^79 ≤ (1787795149/50000000000000 : ℝ)^63
        have hw : |(-2844039/10000000000 : ℝ)|=(2844039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9497200479/10000000000 : ℝ)|^79 ≤ (93735823864961/100000000000000 : ℝ)^63
        have hw : |(9497200479/10000000000 : ℝ)|=(9497200479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s0_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-111433661/10000000000 : ℝ)*x 0 + (-2199281173/5000000000 : ℝ)*x 1 + (3500088289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (111433661/10000000000 : ℝ)^79 ≤ (88912039499/25000000000000 : ℝ)^63 := by
    have hnat : (111433661 : ℕ)^79*25000000000000^63 ≤ 88912039499^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111433661 10000000000 88912039499 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2199281173/5000000000 : ℝ)^79 ≤ (17852252094733/50000000000000 : ℝ)^63 := by
    have hnat : (2199281173 : ℕ)^79*50000000000000^63 ≤ 17852252094733^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199281173 5000000000 17852252094733 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3500088289/5000000000 : ℝ)^79 ≤ (63939847641327/100000000000000 : ℝ)^63 := by
    have hnat : (3500088289 : ℕ)^79*100000000000000^63 ≤ 63939847641327^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3500088289 5000000000 63939847641327 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-111433661/10000000000 : ℝ), (-2199281173/5000000000 : ℝ), (3500088289/5000000000 : ℝ)] ![(88912039499/25000000000000 : ℝ), (17852252094733/50000000000000 : ℝ), (63939847641327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-111433661/10000000000 : ℝ)|^79 ≤ (88912039499/25000000000000 : ℝ)^63
        have hw : |(-111433661/10000000000 : ℝ)|=(111433661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2199281173/5000000000 : ℝ)|^79 ≤ (17852252094733/50000000000000 : ℝ)^63
        have hw : |(-2199281173/5000000000 : ℝ)|=(2199281173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3500088289/5000000000 : ℝ)|^79 ≤ (63939847641327/100000000000000 : ℝ)^63
        have hw : |(3500088289/5000000000 : ℝ)|=(3500088289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s0_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4579797171/5000000000 : ℝ)*x 0 + (641734953/5000000000 : ℝ)*x 1 + (72281321/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4579797171/5000000000 : ℝ)^79 ≤ (17915296950579/20000000000000 : ℝ)^63 := by
    have hnat : (4579797171 : ℕ)^79*20000000000000^63 ≤ 17915296950579^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4579797171 5000000000 17915296950579 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641734953/5000000000 : ℝ)^79 ≤ (761980681051/10000000000000 : ℝ)^63 := by
    have hnat : (641734953 : ℕ)^79*10000000000000^63 ≤ 761980681051^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641734953 5000000000 761980681051 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (72281321/1250000000 : ℝ)^79 ≤ (2803708428567/100000000000000 : ℝ)^63 := by
    have hnat : (72281321 : ℕ)^79*100000000000000^63 ≤ 2803708428567^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72281321 1250000000 2803708428567 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4579797171/5000000000 : ℝ), (641734953/5000000000 : ℝ), (72281321/1250000000 : ℝ)] ![(17915296950579/20000000000000 : ℝ), (761980681051/10000000000000 : ℝ), (2803708428567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4579797171/5000000000 : ℝ)|^79 ≤ (17915296950579/20000000000000 : ℝ)^63
        have hw : |(4579797171/5000000000 : ℝ)|=(4579797171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641734953/5000000000 : ℝ)|^79 ≤ (761980681051/10000000000000 : ℝ)^63
        have hw : |(641734953/5000000000 : ℝ)|=(641734953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(72281321/1250000000 : ℝ)|^79 ≤ (2803708428567/100000000000000 : ℝ)^63
        have hw : |(72281321/1250000000 : ℝ)|=(72281321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s0_16 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5152034347/10000000000 : ℝ)*x 0 + (-250732311/500000000 : ℝ)*x 1 + (-2130086621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152034347/10000000000 : ℝ)^79 ≤ (43534192732057/100000000000000 : ℝ)^63 := by
    have hnat : (5152034347 : ℕ)^79*100000000000000^63 ≤ 43534192732057^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152034347 10000000000 43534192732057 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250732311/500000000 : ℝ)^79 ≤ (4208340304019/10000000000000 : ℝ)^63 := by
    have hnat : (250732311 : ℕ)^79*10000000000000^63 ≤ 4208340304019^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250732311 500000000 4208340304019 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2130086621/10000000000 : ℝ)^79 ≤ (14382404220301/100000000000000 : ℝ)^63 := by
    have hnat : (2130086621 : ℕ)^79*100000000000000^63 ≤ 14382404220301^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130086621 10000000000 14382404220301 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152034347/10000000000 : ℝ), (-250732311/500000000 : ℝ), (-2130086621/10000000000 : ℝ)] ![(43534192732057/100000000000000 : ℝ), (4208340304019/10000000000000 : ℝ), (14382404220301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152034347/10000000000 : ℝ)|^79 ≤ (43534192732057/100000000000000 : ℝ)^63
        have hw : |(5152034347/10000000000 : ℝ)|=(5152034347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-250732311/500000000 : ℝ)|^79 ≤ (4208340304019/10000000000000 : ℝ)^63
        have hw : |(-250732311/500000000 : ℝ)|=(250732311/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2130086621/10000000000 : ℝ)|^79 ≤ (14382404220301/100000000000000 : ℝ)^63
        have hw : |(-2130086621/10000000000 : ℝ)|=(2130086621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s0_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (197629351/2500000000 : ℝ)*x 0 + (-783184277/10000000000 : ℝ)*x 1 + (4668153273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197629351/2500000000 : ℝ)^79 ≤ (1037423152573/25000000000000 : ℝ)^63 := by
    have hnat : (197629351 : ℕ)^79*25000000000000^63 ≤ 1037423152573^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197629351 2500000000 1037423152573 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (783184277/10000000000 : ℝ)^79 ≤ (4101479275177/100000000000000 : ℝ)^63 := by
    have hnat : (783184277 : ℕ)^79*100000000000000^63 ≤ 4101479275177^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783184277 10000000000 4101479275177 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4668153273/5000000000 : ℝ)^79 ≤ (9174882809319/10000000000000 : ℝ)^63 := by
    have hnat : (4668153273 : ℕ)^79*10000000000000^63 ≤ 9174882809319^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4668153273 5000000000 9174882809319 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(197629351/2500000000 : ℝ), (-783184277/10000000000 : ℝ), (4668153273/5000000000 : ℝ)] ![(1037423152573/25000000000000 : ℝ), (4101479275177/100000000000000 : ℝ), (9174882809319/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(197629351/2500000000 : ℝ)|^79 ≤ (1037423152573/25000000000000 : ℝ)^63
        have hw : |(197629351/2500000000 : ℝ)|=(197629351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-783184277/10000000000 : ℝ)|^79 ≤ (4101479275177/100000000000000 : ℝ)^63
        have hw : |(-783184277/10000000000 : ℝ)|=(783184277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4668153273/5000000000 : ℝ)|^79 ≤ (9174882809319/10000000000000 : ℝ)^63
        have hw : |(4668153273/5000000000 : ℝ)|=(4668153273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s0_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-13646643/10000000000 : ℝ)*x 0 + (-8240070521/10000000000 : ℝ)*x 1 + (587627187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13646643/10000000000 : ℝ)^79 ≤ (1596957507/6250000000000 : ℝ)^63 := by
    have hnat : (13646643 : ℕ)^79*6250000000000^63 ≤ 1596957507^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13646643 10000000000 1596957507 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8240070521/10000000000 : ℝ)^79 ≤ (7844767076799/10000000000000 : ℝ)^63 := by
    have hnat : (8240070521 : ℕ)^79*10000000000000^63 ≤ 7844767076799^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8240070521 10000000000 7844767076799 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (587627187/2000000000 : ℝ)^79 ≤ (21526777908743/100000000000000 : ℝ)^63 := by
    have hnat : (587627187 : ℕ)^79*100000000000000^63 ≤ 21526777908743^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587627187 2000000000 21526777908743 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13646643/10000000000 : ℝ), (-8240070521/10000000000 : ℝ), (587627187/2000000000 : ℝ)] ![(1596957507/6250000000000 : ℝ), (7844767076799/10000000000000 : ℝ), (21526777908743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13646643/10000000000 : ℝ)|^79 ≤ (1596957507/6250000000000 : ℝ)^63
        have hw : |(-13646643/10000000000 : ℝ)|=(13646643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8240070521/10000000000 : ℝ)|^79 ≤ (7844767076799/10000000000000 : ℝ)^63
        have hw : |(-8240070521/10000000000 : ℝ)|=(8240070521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(587627187/2000000000 : ℝ)|^79 ≤ (21526777908743/100000000000000 : ℝ)^63
        have hw : |(587627187/2000000000 : ℝ)|=(587627187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s0_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (67964427/80000000 : ℝ)*x 0 + (1606904009/10000000000 : ℝ)*x 1 + (173239673/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67964427/80000000 : ℝ)^79 ≤ (81509570656529/100000000000000 : ℝ)^63 := by
    have hnat : (67964427 : ℕ)^79*100000000000000^63 ≤ 81509570656529^63*80000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67964427 80000000 81509570656529 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1606904009/10000000000 : ℝ)^79 ≤ (2525088435493/25000000000000 : ℝ)^63 := by
    have hnat : (1606904009 : ℕ)^79*25000000000000^63 ≤ 2525088435493^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1606904009 10000000000 2525088435493 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173239673/1250000000 : ℝ)^79 ≤ (4195037795659/50000000000000 : ℝ)^63 := by
    have hnat : (173239673 : ℕ)^79*50000000000000^63 ≤ 4195037795659^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173239673 1250000000 4195037795659 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67964427/80000000 : ℝ), (1606904009/10000000000 : ℝ), (173239673/1250000000 : ℝ)] ![(81509570656529/100000000000000 : ℝ), (2525088435493/25000000000000 : ℝ), (4195037795659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67964427/80000000 : ℝ)|^79 ≤ (81509570656529/100000000000000 : ℝ)^63
        have hw : |(67964427/80000000 : ℝ)|=(67964427/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1606904009/10000000000 : ℝ)|^79 ≤ (2525088435493/25000000000000 : ℝ)^63
        have hw : |(1606904009/10000000000 : ℝ)|=(1606904009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(173239673/1250000000 : ℝ)|^79 ≤ (4195037795659/50000000000000 : ℝ)^63
        have hw : |(173239673/1250000000 : ℝ)|=(173239673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s0_23 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (408436803/2000000000 : ℝ)*x 0 + (-1271096627/2000000000 : ℝ)*x 1 + (-118727461/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408436803/2000000000 : ℝ)^79 ≤ (3410522197531/25000000000000 : ℝ)^63 := by
    have hnat : (408436803 : ℕ)^79*25000000000000^63 ≤ 3410522197531^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408436803 2000000000 3410522197531 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271096627/2000000000 : ℝ)^79 ≤ (2265763352939/4000000000000 : ℝ)^63 := by
    have hnat : (1271096627 : ℕ)^79*4000000000000^63 ≤ 2265763352939^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271096627 2000000000 2265763352939 4000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118727461/312500000 : ℝ)^79 ≤ (14856913686869/50000000000000 : ℝ)^63 := by
    have hnat : (118727461 : ℕ)^79*50000000000000^63 ≤ 14856913686869^63*312500000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118727461 312500000 14856913686869 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(408436803/2000000000 : ℝ), (-1271096627/2000000000 : ℝ), (-118727461/312500000 : ℝ)] ![(3410522197531/25000000000000 : ℝ), (2265763352939/4000000000000 : ℝ), (14856913686869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(408436803/2000000000 : ℝ)|^79 ≤ (3410522197531/25000000000000 : ℝ)^63
        have hw : |(408436803/2000000000 : ℝ)|=(408436803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1271096627/2000000000 : ℝ)|^79 ≤ (2265763352939/4000000000000 : ℝ)^63
        have hw : |(-1271096627/2000000000 : ℝ)|=(1271096627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-118727461/312500000 : ℝ)|^79 ≤ (14856913686869/50000000000000 : ℝ)^63
        have hw : |(-118727461/312500000 : ℝ)|=(118727461/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s0_27 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5341694797/10000000000 : ℝ)*x 0 + (-21469963/5000000000 : ℝ)*x 1 + (3074198183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5341694797/10000000000 : ℝ)^79 ≤ (45553127529599/100000000000000 : ℝ)^63 := by
    have hnat : (5341694797 : ℕ)^79*100000000000000^63 ≤ 45553127529599^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5341694797 10000000000 45553127529599 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21469963/5000000000 : ℝ)^79 ≤ (107568028013/100000000000000 : ℝ)^63 := by
    have hnat : (21469963 : ℕ)^79*100000000000000^63 ≤ 107568028013^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21469963 5000000000 107568028013 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3074198183/5000000000 : ℝ)^79 ≤ (543393044267/1000000000000 : ℝ)^63 := by
    have hnat : (3074198183 : ℕ)^79*1000000000000^63 ≤ 543393044267^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3074198183 5000000000 543393044267 1000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5341694797/10000000000 : ℝ), (-21469963/5000000000 : ℝ), (3074198183/5000000000 : ℝ)] ![(45553127529599/100000000000000 : ℝ), (107568028013/100000000000000 : ℝ), (543393044267/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5341694797/10000000000 : ℝ)|^79 ≤ (45553127529599/100000000000000 : ℝ)^63
        have hw : |(5341694797/10000000000 : ℝ)|=(5341694797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21469963/5000000000 : ℝ)|^79 ≤ (107568028013/100000000000000 : ℝ)^63
        have hw : |(-21469963/5000000000 : ℝ)|=(21469963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3074198183/5000000000 : ℝ)|^79 ≤ (543393044267/1000000000000 : ℝ)^63
        have hw : |(3074198183/5000000000 : ℝ)|=(3074198183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s1_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-624658433/5000000000 : ℝ)*x 0 + (-2953802773/5000000000 : ℝ)*x 1 + (490659379/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (624658433/5000000000 : ℝ)^79 ≤ (7366413971307/100000000000000 : ℝ)^63 := by
    have hnat : (624658433 : ℕ)^79*100000000000000^63 ≤ 7366413971307^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624658433 5000000000 7366413971307 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2953802773/5000000000 : ℝ)^79 ≤ (51684136482041/100000000000000 : ℝ)^63 := by
    have hnat : (2953802773 : ℕ)^79*100000000000000^63 ≤ 51684136482041^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2953802773 5000000000 51684136482041 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490659379/1000000000 : ℝ)^79 ≤ (40949449522081/100000000000000 : ℝ)^63 := by
    have hnat : (490659379 : ℕ)^79*100000000000000^63 ≤ 40949449522081^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490659379 1000000000 40949449522081 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-624658433/5000000000 : ℝ), (-2953802773/5000000000 : ℝ), (490659379/1000000000 : ℝ)] ![(7366413971307/100000000000000 : ℝ), (51684136482041/100000000000000 : ℝ), (40949449522081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-624658433/5000000000 : ℝ)|^79 ≤ (7366413971307/100000000000000 : ℝ)^63
        have hw : |(-624658433/5000000000 : ℝ)|=(624658433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2953802773/5000000000 : ℝ)|^79 ≤ (51684136482041/100000000000000 : ℝ)^63
        have hw : |(-2953802773/5000000000 : ℝ)|=(2953802773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(490659379/1000000000 : ℝ)|^79 ≤ (40949449522081/100000000000000 : ℝ)^63
        have hw : |(490659379/1000000000 : ℝ)|=(490659379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s1_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (394617223/625000000 : ℝ)*x 0 + (1529524867/5000000000 : ℝ)*x 1 + (2900015769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (394617223/625000000 : ℝ)^79 ≤ (7022432286981/12500000000000 : ℝ)^63 := by
    have hnat : (394617223 : ℕ)^79*12500000000000^63 ≤ 7022432286981^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394617223 625000000 7022432286981 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1529524867/5000000000 : ℝ)^79 ≤ (22643410973141/100000000000000 : ℝ)^63 := by
    have hnat : (1529524867 : ℕ)^79*100000000000000^63 ≤ 22643410973141^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1529524867 5000000000 22643410973141 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2900015769/10000000000 : ℝ)^79 ≤ (10588565359001/50000000000000 : ℝ)^63 := by
    have hnat : (2900015769 : ℕ)^79*50000000000000^63 ≤ 10588565359001^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2900015769 10000000000 10588565359001 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(394617223/625000000 : ℝ), (1529524867/5000000000 : ℝ), (2900015769/10000000000 : ℝ)] ![(7022432286981/12500000000000 : ℝ), (22643410973141/100000000000000 : ℝ), (10588565359001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(394617223/625000000 : ℝ)|^79 ≤ (7022432286981/12500000000000 : ℝ)^63
        have hw : |(394617223/625000000 : ℝ)|=(394617223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1529524867/5000000000 : ℝ)|^79 ≤ (22643410973141/100000000000000 : ℝ)^63
        have hw : |(1529524867/5000000000 : ℝ)|=(1529524867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2900015769/10000000000 : ℝ)|^79 ≤ (10588565359001/50000000000000 : ℝ)^63
        have hw : |(2900015769/10000000000 : ℝ)|=(2900015769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s1_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1255547323/2500000000 : ℝ)*x 0 + (-3837451717/10000000000 : ℝ)*x 1 + (-359750581/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1255547323/2500000000 : ℝ)^79 ≤ (10540699286561/25000000000000 : ℝ)^63 := by
    have hnat : (1255547323 : ℕ)^79*25000000000000^63 ≤ 10540699286561^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255547323 2500000000 10540699286561 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3837451717/10000000000 : ℝ)^79 ≤ (30088672823813/100000000000000 : ℝ)^63 := by
    have hnat : (3837451717 : ℕ)^79*100000000000000^63 ≤ 30088672823813^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3837451717 10000000000 30088672823813 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (359750581/1000000000 : ℝ)^79 ≤ (27748530014351/100000000000000 : ℝ)^63 := by
    have hnat : (359750581 : ℕ)^79*100000000000000^63 ≤ 27748530014351^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359750581 1000000000 27748530014351 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1255547323/2500000000 : ℝ), (-3837451717/10000000000 : ℝ), (-359750581/1000000000 : ℝ)] ![(10540699286561/25000000000000 : ℝ), (30088672823813/100000000000000 : ℝ), (27748530014351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1255547323/2500000000 : ℝ)|^79 ≤ (10540699286561/25000000000000 : ℝ)^63
        have hw : |(1255547323/2500000000 : ℝ)|=(1255547323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3837451717/10000000000 : ℝ)|^79 ≤ (30088672823813/100000000000000 : ℝ)^63
        have hw : |(-3837451717/10000000000 : ℝ)|=(3837451717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-359750581/1000000000 : ℝ)|^79 ≤ (27748530014351/100000000000000 : ℝ)^63
        have hw : |(-359750581/1000000000 : ℝ)|=(359750581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318075_s1_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3237696087/10000000000 : ℝ)*x 0 + (-2659707053/10000000000 : ℝ)*x 1 + (635923303/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3237696087/10000000000 : ℝ)^79 ≤ (12156865090867/50000000000000 : ℝ)^63 := by
    have hnat : (3237696087 : ℕ)^79*50000000000000^63 ≤ 12156865090867^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3237696087 10000000000 12156865090867 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2659707053/10000000000 : ℝ)^79 ≤ (3800054684153/20000000000000 : ℝ)^63 := by
    have hnat : (2659707053 : ℕ)^79*20000000000000^63 ≤ 3800054684153^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2659707053 10000000000 3800054684153 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (635923303/1000000000 : ℝ)^79 ≤ (14171499095391/25000000000000 : ℝ)^63 := by
    have hnat : (635923303 : ℕ)^79*25000000000000^63 ≤ 14171499095391^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635923303 1000000000 14171499095391 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3237696087/10000000000 : ℝ), (-2659707053/10000000000 : ℝ), (635923303/1000000000 : ℝ)] ![(12156865090867/50000000000000 : ℝ), (3800054684153/20000000000000 : ℝ), (14171499095391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3237696087/10000000000 : ℝ)|^79 ≤ (12156865090867/50000000000000 : ℝ)^63
        have hw : |(3237696087/10000000000 : ℝ)|=(3237696087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2659707053/10000000000 : ℝ)|^79 ≤ (3800054684153/20000000000000 : ℝ)^63
        have hw : |(-2659707053/10000000000 : ℝ)|=(2659707053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(635923303/1000000000 : ℝ)|^79 ≤ (14171499095391/25000000000000 : ℝ)^63
        have hw : |(635923303/1000000000 : ℝ)|=(635923303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318075 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]]) : False := by
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
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (34269/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
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
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(499901486224611/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1147839/100000000 : ℝ)*X 0 0+(-6970827659/10000000000 : ℝ)*X 0 1+(2215109299/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2770571123/5000000000 : ℝ)*X 2 0+(-1781651083/5000000000 : ℝ)*X 2 1+(-824579043/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-191179123/5000000000 : ℝ)*X 0 0+(-516553581/625000000 : ℝ)*X 0 1+(681258363/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((5605627421/10000000000 : ℝ)*X 1 0+(1116768669/2500000000 : ℝ)*X 1 1+(1113271069/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((266064573/400000000 : ℝ)*X 2 0+(-3070518129/10000000000 : ℝ)*X 2 1+(-616376197/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1097335267/10000000000 : ℝ)*X 0 0+(-2844039/10000000000 : ℝ)*X 0 1+(9497200479/10000000000 : ℝ)*X 0 2+(1097335267/10000000000 : ℝ)*X 1 0+(-2844039/10000000000 : ℝ)*X 1 1+(9497200479/10000000000 : ℝ)*X 1 2+(1097335267/10000000000 : ℝ)*X 2 0+(-2844039/10000000000 : ℝ)*X 2 1+(9497200479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-111433661/10000000000 : ℝ)*X 0 0+(-2199281173/5000000000 : ℝ)*X 0 1+(3500088289/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4579797171/5000000000 : ℝ)*X 1 0+(641734953/5000000000 : ℝ)*X 1 1+(72281321/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((5152034347/10000000000 : ℝ)*X 2 0+(-250732311/500000000 : ℝ)*X 2 1+(-2130086621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((197629351/2500000000 : ℝ)*X 0 0+(-783184277/10000000000 : ℝ)*X 0 1+(4668153273/5000000000 : ℝ)*X 0 2+(197629351/2500000000 : ℝ)*X 1 0+(-783184277/10000000000 : ℝ)*X 1 1+(4668153273/5000000000 : ℝ)*X 1 2+(197629351/2500000000 : ℝ)*X 2 0+(-783184277/10000000000 : ℝ)*X 2 1+(4668153273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-13646643/10000000000 : ℝ)*X 0 0+(-8240070521/10000000000 : ℝ)*X 0 1+(587627187/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((67964427/80000000 : ℝ)*X 1 0+(1606904009/10000000000 : ℝ)*X 1 1+(173239673/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((408436803/2000000000 : ℝ)*X 2 0+(-1271096627/2000000000 : ℝ)*X 2 1+(-118727461/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((5341694797/10000000000 : ℝ)*X 0 0+(-21469963/5000000000 : ℝ)*X 0 1+(3074198183/5000000000 : ℝ)*X 0 2+(5341694797/10000000000 : ℝ)*X 1 0+(-21469963/5000000000 : ℝ)*X 1 1+(3074198183/5000000000 : ℝ)*X 1 2+(5341694797/10000000000 : ℝ)*X 2 0+(-21469963/5000000000 : ℝ)*X 2 1+(3074198183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((64001/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(64001/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (38109777667857145299987/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (144119965047/250000000000 : ℝ)*(base7) + (456567/200000000000 : ℝ)*(base31) + (82864447/8000000000 : ℝ)*(base33) + (199531714399/1000000000000 : ℝ)*(base43) + (378212859087/500000000000 : ℝ)*(base54) + (1516422199/40000000000 : ℝ)*(base59) + (1983769795547/1000000000000 : ℝ)*(major_s0_0) + (1794596137023/1000000000000 : ℝ)*(major_s0_1) + (2417386979/1953125000 : ℝ)*(major_s0_2) + (959551/100000000000 : ℝ)*(sp_s0_0) + (236663034247/100000000000 : ℝ)*(sp_s0_7) + (2555813596503/1000000000000 : ℝ)*(sp_s0_8) + (159985616393/100000000000 : ℝ)*(sp_s0_9) + (912874356191/1000000000000 : ℝ)*(sp_s0_13) + (273205624253/250000000000 : ℝ)*(f.failure) + (1283085826189/500000000000 : ℝ)*(f.sum) + (56754311814503/1000000000000000000000000000 : ℝ)*base63 + (120031670329171/156250000000000000000000000 : ℝ)*base65 + (228803212117157/5000000000000000000000000000 : ℝ)*base66 + (5740109290803/19531250000000000000000000 : ℝ)*base69 + (526839964376999/5000000000000000000000000000 : ℝ)*base71 + (817620938107217/5000000000000000000000000000 : ℝ)*base73 + (1936458265626947/5000000000000000000000000000 : ℝ)*base75 + (1820732842343527/5000000000000000000000000000 : ℝ)*base77 + (25702684625497/250000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (647/1000000000000000 : ℝ)*base87 + (647/1000000000000000 : ℝ)*base89 + (647/1000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-74121/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-74121/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (149461934774464355637/25000000000000000000000000 : ℝ) := by norm_num
    linear_combination (406213601949/500000000000 : ℝ)*(base7) + (2876479/250000000000 : ℝ)*(base31) + (17470034061/25000000000 : ℝ)*(base33) + (1181057/500000000000 : ℝ)*(base40) + (30660850407/1000000000000 : ℝ)*(base60) + (40513944363/50000000000 : ℝ)*(major_s0_0) + (15090802497/10000000000 : ℝ)*(major_s0_1) + (15090802497/10000000000 : ℝ)*(major_s0_2) + (21482839/1000000000000 : ℝ)*(sp_s0_2) + (345426826597/200000000000 : ℝ)*(sp_s0_14) + (514166299181/500000000000 : ℝ)*(sp_s0_15) + (514155643853/500000000000 : ℝ)*(sp_s0_16) + (1639422274061/1000000000000 : ℝ)*(sp_s0_20) + (86091/500000000000 : ℝ)*(sp_s0_22) + (827006576079/1000000000000 : ℝ)*(f.failure) + (345426826597/200000000000 : ℝ)*(f.sum) + (720342353519/5000000000000000000000000 : ℝ)*base62 + (14317826881333/50000000000000000000000000 : ℝ)*base65 + (14611037266523/50000000000000000000000000 : ℝ)*base66 + (21745907423477/50000000000000000000000000 : ℝ)*base69 + (401142611191/1953125000000000000000000 : ℝ)*base71 + (107341144932207/250000000000000000000000000 : ℝ)*base72 + (4050841753667/50000000000000000000000000 : ℝ)*base74 + (196296967600783/250000000000000000000000000 : ℝ)*base77 + (5817367207411/125000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (621/4000000000000000 : ℝ)*base87 + (621/4000000000000000 : ℝ)*base89 + (621/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70461/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(70461/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (587681492637376448433/39062500000000000000000000 : ℝ) := by norm_num
    linear_combination (273447837829/500000000000 : ℝ)*(base7) + (506226158313/1000000000000 : ℝ)*(base33) + (185688949183/500000000000 : ℝ)*(base40) + (5028851473/50000000000 : ℝ)*(base43) + (145831874639/1000000000000 : ℝ)*(base49) + (64377/62500000000 : ℝ)*(base59) + (379137757137/200000000000 : ℝ)*(major_s0_0) + (1150668957269/500000000000 : ℝ)*(major_s0_1) + (1200957471999/500000000000 : ℝ)*(major_s0_2) + (11847477/1000000000000 : ℝ)*(sp_s0_0) + (3074578438677/1000000000000 : ℝ)*(sp_s0_21) + (2668941157301/1000000000000 : ℝ)*(sp_s0_22) + (2568364127841/1000000000000 : ℝ)*(sp_s0_23) + (931596883999/500000000000 : ℝ)*(sp_s0_27) + (65814904617/50000000000 : ℝ)*(f.failure) + (3175167315613/1000000000000 : ℝ)*(f.sum) + (5837230918083/25000000000000000000000000 : ℝ)*base63 + (1750799544832611/2500000000000000000000000000 : ℝ)*base65 + (170532468647271/2500000000000000000000000000 : ℝ)*base66 + (1283288134544341/2500000000000000000000000000 : ℝ)*base68 + (985684799593807/5000000000000000000000000000 : ℝ)*base71 + (276555234901293/1000000000000000000000000000 : ℝ)*base72 + (191401099602641/2500000000000000000000000000 : ℝ)*base75 + (591434787185717/1000000000000000000000000000 : ℝ)*base77 + (1403848349301007/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (117/200000000000000 : ℝ)*base86 + (117/200000000000000 : ℝ)*base88 + (117/200000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (64001/100000 : ℝ) ^ (39/8 : ℝ) ≤ (5677151164660574651/50000000000000000000 : ℝ) := by
    have hpowers : (64001/100000 : ℝ)^39 ≤ (5677151164660574651/50000000000000000000 : ℝ)^8 := by
      have hnat : (64001 : ℕ)^39*50000000000000000000^8 ≤ 5677151164660574651^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64001 100000 5677151164660574651 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64001/100000 : ℝ)) (X := (5677151164660574651/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (55677151164660574651/50000000000000000000 : ℝ) ≤ (10223060320711039/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (55677151164660574651/50000000000000000000 : ℝ)^8 ≤ (10223060320711039/10000000000000000 : ℝ)^39 := by
      have hnat : (55677151164660574651 : ℕ)^8*10000000000000000^39 ≤ 10223060320711039^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55677151164660574651 50000000000000000000 10223060320711039 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10223060320711039/10000000000000000 : ℝ)) (X := (55677151164660574651/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (30677151164660574651/25000000000000000000 : ℝ) ≤ (1042871437110127/1000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (30677151164660574651/25000000000000000000 : ℝ)^8 ≤ (1042871437110127/1000000000000000 : ℝ)^39 := by
      have hnat : (30677151164660574651 : ℕ)^8*1000000000000000^39 ≤ 1042871437110127^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30677151164660574651 25000000000000000000 1042871437110127 1000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1042871437110127/1000000000000000 : ℝ)) (X := (30677151164660574651/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(31865760101577/914300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(205654050390231/6400100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (64001/100000 : ℝ)) (alpha := (31865760101577/914300000000000 : ℝ)) (beta := (205654050390231/6400100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (64001/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(31865760101577/914300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(205654050390231/6400100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (74121/100000 : ℝ) ^ (39/8 : ℝ) ≤ (11612713065581779613/50000000000000000000 : ℝ) := by
    have hpowers : (74121/100000 : ℝ)^39 ≤ (11612713065581779613/50000000000000000000 : ℝ)^8 := by
      have hnat : (74121 : ℕ)^39*50000000000000000000^8 ≤ 11612713065581779613^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74121 100000 11612713065581779613 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74121/100000 : ℝ)) (X := (11612713065581779613/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (61612713065581779613/50000000000000000000 : ℝ) ≤ (1304713657837719/1250000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (61612713065581779613/50000000000000000000 : ℝ)^8 ≤ (1304713657837719/1250000000000000 : ℝ)^39 := by
      have hnat : (61612713065581779613 : ℕ)^8*1250000000000000^39 ≤ 1304713657837719^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61612713065581779613 50000000000000000000 1304713657837719 1250000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1304713657837719/1250000000000000 : ℝ)) (X := (61612713065581779613/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (36612713065581779613/25000000000000000000 : ℝ) ≤ (2162808553241877/2000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (36612713065581779613/25000000000000000000 : ℝ)^8 ≤ (2162808553241877/2000000000000000 : ℝ)^39 := by
      have hnat : (36612713065581779613 : ℕ)^8*2000000000000000^39 ≤ 2162808553241877^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36612713065581779613 25000000000000000000 2162808553241877 2000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2162808553241877/2000000000000000 : ℝ)) (X := (36612713065581779613/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(54713657837719/926512500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(125444501169211/2470700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (74121/100000 : ℝ)) (alpha := (54713657837719/926512500000000 : ℝ)) (beta := (125444501169211/2470700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (74121/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(54713657837719/926512500000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(125444501169211/2470700000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (70461/100000 : ℝ) ^ (39/8 : ℝ) ≤ (3628945181768295599/20000000000000000000 : ℝ) := by
    have hpowers : (70461/100000 : ℝ)^39 ≤ (3628945181768295599/20000000000000000000 : ℝ)^8 := by
      have hnat : (70461 : ℕ)^39*20000000000000000000^8 ≤ 3628945181768295599^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70461 100000 3628945181768295599 20000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (70461/100000 : ℝ)) (X := (3628945181768295599/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (23628945181768295599/20000000000000000000 : ℝ) ≤ (10347947660420969/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (23628945181768295599/20000000000000000000 : ℝ)^8 ≤ (10347947660420969/10000000000000000 : ℝ)^39 := by
      have hnat : (23628945181768295599 : ℕ)^8*10000000000000000^39 ≤ 10347947660420969^39*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23628945181768295599 20000000000000000000 10347947660420969 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10347947660420969/10000000000000000 : ℝ)) (X := (23628945181768295599/20000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (13628945181768295599/10000000000000000000 : ℝ) ≤ (2131140068809283/2000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (13628945181768295599/10000000000000000000 : ℝ)^8 ≤ (2131140068809283/2000000000000000 : ℝ)^39 := by
      have hnat : (13628945181768295599 : ℕ)^8*2000000000000000^39 ≤ 2131140068809283^39*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13628945181768295599 10000000000000000000 2131140068809283 2000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2131140068809283/2000000000000000 : ℝ)) (X := (13628945181768295599/10000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(347947660420969/7046100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(153876341812723/3523050000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (70461/100000 : ℝ)) (alpha := (347947660420969/7046100000000000 : ℝ)) (beta := (153876341812723/3523050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (70461/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(347947660420969/7046100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(153876341812723/3523050000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-624658433/5000000000 : ℝ)*X 0 0+(-2953802773/5000000000 : ℝ)*X 0 1+(490659379/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((394617223/625000000 : ℝ)*X 1 0+(1529524867/5000000000 : ℝ)*X 1 1+(2900015769/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1255547323/2500000000 : ℝ)*X 2 0+(-3837451717/10000000000 : ℝ)*X 2 1+(-359750581/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3237696087/10000000000 : ℝ)*X 0 0+(-2659707053/10000000000 : ℝ)*X 0 1+(635923303/1000000000 : ℝ)*X 0 2+(3237696087/10000000000 : ℝ)*X 1 0+(-2659707053/10000000000 : ℝ)*X 1 1+(635923303/1000000000 : ℝ)*X 1 2+(3237696087/10000000000 : ℝ)*X 2 0+(-2659707053/10000000000 : ℝ)*X 2 1+(635923303/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318075_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15897/2000 : ℝ) < ((-7299/4000 : ℝ)*P 0+(-7299/4000 : ℝ)*P 1+(-7299/4000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15897/2000 : ℝ) < (-2453550370177010590969753397344416033/309494600577575000000000000000000000 : ℝ) := by norm_num
    linear_combination (333/200000000000 : ℝ)*(base13) + (1519/1000000000000 : ℝ)*(base24) + (59/62500000000 : ℝ)*(base33) + (60140268477/125000000000 : ℝ)*(base40) + (10150228893/125000000000 : ℝ)*(base49) + (1/12500000000 : ℝ)*(base50) + (77373869589/1000000000000 : ℝ)*(base60) + (114046874941/62500000000 : ℝ)*(major_s1_0) + (7299/4000 : ℝ)*(major_s1_1) + (7299/4000 : ℝ)*(major_s1_2) + (2642534380041/1000000000000 : ℝ)*(sp_s1_0) + (2642534380763/1000000000000 : ℝ)*(sp_s1_1) + (2642534379909/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1321267190853/500000000000 : ℝ)*(f.sum) + (499916056245274441/967155515000000000000000000000 : ℝ)*base62 + (16233618237503/39145000000000000000000000 : ℝ)*base64 + (1024176495073/24707000000000000000000000 : ℝ)*base66 + (4481604028021/4893125000000000000000000 : ℝ)*base68 + (384895747964714523/1789513675000000000000000000000 : ℝ)*base70 + (846270469487767/3200050000000000000000000000 : ℝ)*base72 + (41176931135878149/61767500000000000000000000 : ℝ)*base74 + (5108008874051/457150000000000000000000000 : ℝ)*base77 + (30295265185431251737/39531817675000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (333/500000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p018_b033 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (c : Fin 88) (hlo : 75 ≤ c.val) (hhi : c.val < 76)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=75 := by omega
  rcases hc with rfl
  · exact collision_c318075 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (c : Fin 88) (hlo : 75 ≤ c.val) (hhi : c.val < 76)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p018_b033 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

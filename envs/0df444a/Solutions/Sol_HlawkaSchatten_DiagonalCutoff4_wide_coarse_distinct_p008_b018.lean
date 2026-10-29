-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p008_b018
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:43:07.357088+00:00
-- url     : https://prove2.me/submissions/c1e3a81a-6147-43d9-a465-8065e70c8615

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
theorem collision_support_c308029_s0_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3993742303/10000000000 : ℝ)*x 0 + (60527131/156250000 : ℝ)*x 1 + (198510347/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3993742303/10000000000 : ℝ)^35 ≤ (3803473837653/12500000000000 : ℝ)^27 := by
    have hnat : (3993742303 : ℕ)^35*12500000000000^27 ≤ 3803473837653^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3993742303 10000000000 3803473837653 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60527131/156250000 : ℝ)^35 ≤ (29247888993887/100000000000000 : ℝ)^27 := by
    have hnat : (60527131 : ℕ)^35*100000000000000^27 ≤ 29247888993887^27*156250000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60527131 156250000 29247888993887 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198510347/400000000 : ℝ)^35 ≤ (2016216014493/5000000000000 : ℝ)^27 := by
    have hnat : (198510347 : ℕ)^35*5000000000000^27 ≤ 2016216014493^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198510347 400000000 2016216014493 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3993742303/10000000000 : ℝ), (60527131/156250000 : ℝ), (198510347/400000000 : ℝ)] ![(3803473837653/12500000000000 : ℝ), (29247888993887/100000000000000 : ℝ), (2016216014493/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3993742303/10000000000 : ℝ)|^35 ≤ (3803473837653/12500000000000 : ℝ)^27
        have hw : |(-3993742303/10000000000 : ℝ)|=(3993742303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(60527131/156250000 : ℝ)|^35 ≤ (29247888993887/100000000000000 : ℝ)^27
        have hw : |(60527131/156250000 : ℝ)|=(60527131/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(198510347/400000000 : ℝ)|^35 ≤ (2016216014493/5000000000000 : ℝ)^27
        have hw : |(198510347/400000000 : ℝ)|=(198510347/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s0_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6134044837/10000000000 : ℝ)*x 0 + (-1025191739/10000000000 : ℝ)*x 1 + (2546834221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6134044837/10000000000 : ℝ)^35 ≤ (53070985511201/100000000000000 : ℝ)^27 := by
    have hnat : (6134044837 : ℕ)^35*100000000000000^27 ≤ 53070985511201^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6134044837 10000000000 53070985511201 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025191739/10000000000 : ℝ)^35 ≤ (652559813537/12500000000000 : ℝ)^27 := by
    have hnat : (1025191739 : ℕ)^35*12500000000000^27 ≤ 652559813537^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025191739 10000000000 652559813537 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2546834221/5000000000 : ℝ)^35 ≤ (20854267981091/50000000000000 : ℝ)^27 := by
    have hnat : (2546834221 : ℕ)^35*50000000000000^27 ≤ 20854267981091^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2546834221 5000000000 20854267981091 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6134044837/10000000000 : ℝ), (-1025191739/10000000000 : ℝ), (2546834221/5000000000 : ℝ)] ![(53070985511201/100000000000000 : ℝ), (652559813537/12500000000000 : ℝ), (20854267981091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6134044837/10000000000 : ℝ)|^35 ≤ (53070985511201/100000000000000 : ℝ)^27
        have hw : |(6134044837/10000000000 : ℝ)|=(6134044837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1025191739/10000000000 : ℝ)|^35 ≤ (652559813537/12500000000000 : ℝ)^27
        have hw : |(-1025191739/10000000000 : ℝ)|=(1025191739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2546834221/5000000000 : ℝ)|^35 ≤ (20854267981091/50000000000000 : ℝ)^27
        have hw : |(2546834221/5000000000 : ℝ)|=(2546834221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s0_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (956262057/5000000000 : ℝ)*x 0 + (3912251201/5000000000 : ℝ)*x 1 + (-2376566869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (956262057/5000000000 : ℝ)^35 ≤ (2928800023293/25000000000000 : ℝ)^27 := by
    have hnat : (956262057 : ℕ)^35*25000000000000^27 ≤ 2928800023293^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956262057 5000000000 2928800023293 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3912251201/5000000000 : ℝ)^35 ≤ (363796365313/500000000000 : ℝ)^27 := by
    have hnat : (3912251201 : ℕ)^35*500000000000^27 ≤ 363796365313^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3912251201 5000000000 363796365313 500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2376566869/10000000000 : ℝ)^35 ≤ (15525526832753/100000000000000 : ℝ)^27 := by
    have hnat : (2376566869 : ℕ)^35*100000000000000^27 ≤ 15525526832753^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2376566869 10000000000 15525526832753 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(956262057/5000000000 : ℝ), (3912251201/5000000000 : ℝ), (-2376566869/10000000000 : ℝ)] ![(2928800023293/25000000000000 : ℝ), (363796365313/500000000000 : ℝ), (15525526832753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(956262057/5000000000 : ℝ)|^35 ≤ (2928800023293/25000000000000 : ℝ)^27
        have hw : |(956262057/5000000000 : ℝ)|=(956262057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3912251201/5000000000 : ℝ)|^35 ≤ (363796365313/500000000000 : ℝ)^27
        have hw : |(3912251201/5000000000 : ℝ)|=(3912251201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2376566869/10000000000 : ℝ)|^35 ≤ (15525526832753/100000000000000 : ℝ)^27
        have hw : |(-2376566869/10000000000 : ℝ)|=(2376566869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s0_4 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^35 ≤ (0 : ℝ)^27 := by
    have hnat : (0 : ℕ)^35*1^27 ≤ 0^27*1^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^35 ≤ (1 : ℝ)^27 := by
    have hnat : (1 : ℕ)^35*1^27 ≤ 1^27*1^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^35 ≤ (0 : ℝ)^27 := by
    have hnat : (0 : ℕ)^35*1^27 ≤ 0^27*1^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^35 ≤ (0 : ℝ)^27
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1 : ℝ)|^35 ≤ (1 : ℝ)^27
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^35 ≤ (0 : ℝ)^27
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s0_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2092732173/5000000000 : ℝ)*x 0 + (2850384109/10000000000 : ℝ)*x 1 + (1419508701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092732173/5000000000 : ℝ)^35 ≤ (16167307348323/50000000000000 : ℝ)^27 := by
    have hnat : (2092732173 : ℕ)^35*50000000000000^27 ≤ 16167307348323^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092732173 5000000000 16167307348323 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2850384109/10000000000 : ℝ)^35 ≤ (9825695140581/50000000000000 : ℝ)^27 := by
    have hnat : (2850384109 : ℕ)^35*50000000000000^27 ≤ 9825695140581^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850384109 10000000000 9825695140581 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1419508701/2500000000 : ℝ)^35 ≤ (960279900007/2000000000000 : ℝ)^27 := by
    have hnat : (1419508701 : ℕ)^35*2000000000000^27 ≤ 960279900007^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419508701 2500000000 960279900007 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2092732173/5000000000 : ℝ), (2850384109/10000000000 : ℝ), (1419508701/2500000000 : ℝ)] ![(16167307348323/50000000000000 : ℝ), (9825695140581/50000000000000 : ℝ), (960279900007/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2092732173/5000000000 : ℝ)|^35 ≤ (16167307348323/50000000000000 : ℝ)^27
        have hw : |(-2092732173/5000000000 : ℝ)|=(2092732173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2850384109/10000000000 : ℝ)|^35 ≤ (9825695140581/50000000000000 : ℝ)^27
        have hw : |(2850384109/10000000000 : ℝ)|=(2850384109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1419508701/2500000000 : ℝ)|^35 ≤ (960279900007/2000000000000 : ℝ)^27
        have hw : |(1419508701/2500000000 : ℝ)|=(1419508701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s0_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1376538279/2500000000 : ℝ)*x 0 + (-51447047/2000000000 : ℝ)*x 1 + (6127000869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1376538279/2500000000 : ℝ)^35 ≤ (9227681289929/20000000000000 : ℝ)^27 := by
    have hnat : (1376538279 : ℕ)^35*20000000000000^27 ≤ 9227681289929^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376538279 2500000000 9227681289929 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51447047/2000000000 : ℝ)^35 ≤ (54349715533/6250000000000 : ℝ)^27 := by
    have hnat : (51447047 : ℕ)^35*6250000000000^27 ≤ 54349715533^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51447047 2000000000 54349715533 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6127000869/10000000000 : ℝ)^35 ≤ (66239997609/125000000000 : ℝ)^27 := by
    have hnat : (6127000869 : ℕ)^35*125000000000^27 ≤ 66239997609^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6127000869 10000000000 66239997609 125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1376538279/2500000000 : ℝ), (-51447047/2000000000 : ℝ), (6127000869/10000000000 : ℝ)] ![(9227681289929/20000000000000 : ℝ), (54349715533/6250000000000 : ℝ), (66239997609/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1376538279/2500000000 : ℝ)|^35 ≤ (9227681289929/20000000000000 : ℝ)^27
        have hw : |(1376538279/2500000000 : ℝ)|=(1376538279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51447047/2000000000 : ℝ)|^35 ≤ (54349715533/6250000000000 : ℝ)^27
        have hw : |(-51447047/2000000000 : ℝ)|=(51447047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6127000869/10000000000 : ℝ)|^35 ≤ (66239997609/125000000000 : ℝ)^27
        have hw : |(6127000869/10000000000 : ℝ)|=(6127000869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s0_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (294669163/5000000000 : ℝ)*x 0 + (4754066023/5000000000 : ℝ)*x 1 + (-799501143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (294669163/5000000000 : ℝ)^35 ≤ (1273498095791/50000000000000 : ℝ)^27 := by
    have hnat : (294669163 : ℕ)^35*50000000000000^27 ≤ 1273498095791^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294669163 5000000000 1273498095791 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4754066023/5000000000 : ℝ)^35 ≤ (93670943493773/100000000000000 : ℝ)^27 := by
    have hnat : (4754066023 : ℕ)^35*100000000000000^27 ≤ 93670943493773^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4754066023 5000000000 93670943493773 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (799501143/10000000000 : ℝ)^35 ≤ (1891030149309/50000000000000 : ℝ)^27 := by
    have hnat : (799501143 : ℕ)^35*50000000000000^27 ≤ 1891030149309^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      799501143 10000000000 1891030149309 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(294669163/5000000000 : ℝ), (4754066023/5000000000 : ℝ), (-799501143/10000000000 : ℝ)] ![(1273498095791/50000000000000 : ℝ), (93670943493773/100000000000000 : ℝ), (1891030149309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(294669163/5000000000 : ℝ)|^35 ≤ (1273498095791/50000000000000 : ℝ)^27
        have hw : |(294669163/5000000000 : ℝ)|=(294669163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4754066023/5000000000 : ℝ)|^35 ≤ (93670943493773/100000000000000 : ℝ)^27
        have hw : |(4754066023/5000000000 : ℝ)|=(4754066023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-799501143/10000000000 : ℝ)|^35 ≤ (1891030149309/50000000000000 : ℝ)^27
        have hw : |(-799501143/10000000000 : ℝ)|=(799501143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s0_12 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (498913079/1250000000 : ℝ)*x 0 + (1104352797/2500000000 : ℝ)*x 1 + (4441345243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (498913079/1250000000 : ℝ)^35 ≤ (7600929421729/25000000000000 : ℝ)^27 := by
    have hnat : (498913079 : ℕ)^35*25000000000000^27 ≤ 7600929421729^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498913079 1250000000 7600929421729 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104352797/2500000000 : ℝ)^35 ≤ (433453367223/1250000000000 : ℝ)^27 := by
    have hnat : (1104352797 : ℕ)^35*1250000000000^27 ≤ 433453367223^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104352797 2500000000 433453367223 1250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4441345243/10000000000 : ℝ)^35 ≤ (34920012924377/100000000000000 : ℝ)^27 := by
    have hnat : (4441345243 : ℕ)^35*100000000000000^27 ≤ 34920012924377^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4441345243 10000000000 34920012924377 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(498913079/1250000000 : ℝ), (1104352797/2500000000 : ℝ), (4441345243/10000000000 : ℝ)] ![(7600929421729/25000000000000 : ℝ), (433453367223/1250000000000 : ℝ), (34920012924377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(498913079/1250000000 : ℝ)|^35 ≤ (7600929421729/25000000000000 : ℝ)^27
        have hw : |(498913079/1250000000 : ℝ)|=(498913079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1104352797/2500000000 : ℝ)|^35 ≤ (433453367223/1250000000000 : ℝ)^27
        have hw : |(1104352797/2500000000 : ℝ)|=(1104352797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4441345243/10000000000 : ℝ)|^35 ≤ (34920012924377/100000000000000 : ℝ)^27
        have hw : |(4441345243/10000000000 : ℝ)|=(4441345243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s0_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-4876010521/10000000000 : ℝ)*x 0 + (1224619621/5000000000 : ℝ)*x 1 + (5349432663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4876010521/10000000000 : ℝ)^35 ≤ (39412986122383/100000000000000 : ℝ)^27 := by
    have hnat : (4876010521 : ℕ)^35*100000000000000^27 ≤ 39412986122383^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4876010521 10000000000 39412986122383 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1224619621/5000000000 : ℝ)^35 ≤ (16143712669111/100000000000000 : ℝ)^27 := by
    have hnat : (1224619621 : ℕ)^35*100000000000000^27 ≤ 16143712669111^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1224619621 5000000000 16143712669111 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5349432663/10000000000 : ℝ)^35 ≤ (22221650597929/50000000000000 : ℝ)^27 := by
    have hnat : (5349432663 : ℕ)^35*50000000000000^27 ≤ 22221650597929^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349432663 10000000000 22221650597929 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4876010521/10000000000 : ℝ), (1224619621/5000000000 : ℝ), (5349432663/10000000000 : ℝ)] ![(39412986122383/100000000000000 : ℝ), (16143712669111/100000000000000 : ℝ), (22221650597929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4876010521/10000000000 : ℝ)|^35 ≤ (39412986122383/100000000000000 : ℝ)^27
        have hw : |(-4876010521/10000000000 : ℝ)|=(4876010521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1224619621/5000000000 : ℝ)|^35 ≤ (16143712669111/100000000000000 : ℝ)^27
        have hw : |(1224619621/5000000000 : ℝ)|=(1224619621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5349432663/10000000000 : ℝ)|^35 ≤ (22221650597929/50000000000000 : ℝ)^27
        have hw : |(5349432663/10000000000 : ℝ)|=(5349432663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s0_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1829097901/2500000000 : ℝ)*x 0 + (-1216443883/10000000000 : ℝ)*x 1 + (362003799/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1829097901/2500000000 : ℝ)^35 ≤ (8336785785873/12500000000000 : ℝ)^27 := by
    have hnat : (1829097901 : ℕ)^35*12500000000000^27 ≤ 8336785785873^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1829097901 2500000000 8336785785873 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1216443883/10000000000 : ℝ)^35 ≤ (203637741647/3125000000000 : ℝ)^27 := by
    have hnat : (1216443883 : ℕ)^35*3125000000000^27 ≤ 203637741647^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216443883 10000000000 203637741647 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (362003799/1000000000 : ℝ)^35 ≤ (13394652984637/50000000000000 : ℝ)^27 := by
    have hnat : (362003799 : ℕ)^35*50000000000000^27 ≤ 13394652984637^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362003799 1000000000 13394652984637 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1829097901/2500000000 : ℝ), (-1216443883/10000000000 : ℝ), (362003799/1000000000 : ℝ)] ![(8336785785873/12500000000000 : ℝ), (203637741647/3125000000000 : ℝ), (13394652984637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1829097901/2500000000 : ℝ)|^35 ≤ (8336785785873/12500000000000 : ℝ)^27
        have hw : |(1829097901/2500000000 : ℝ)|=(1829097901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1216443883/10000000000 : ℝ)|^35 ≤ (203637741647/3125000000000 : ℝ)^27
        have hw : |(-1216443883/10000000000 : ℝ)|=(1216443883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(362003799/1000000000 : ℝ)|^35 ≤ (13394652984637/50000000000000 : ℝ)^27
        have hw : |(362003799/1000000000 : ℝ)|=(362003799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s0_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (29150451/250000000 : ℝ)*x 0 + (3998565281/5000000000 : ℝ)*x 1 + (-1387744131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29150451/250000000 : ℝ)^35 ≤ (3084206882867/50000000000000 : ℝ)^27 := by
    have hnat : (29150451 : ℕ)^35*50000000000000^27 ≤ 3084206882867^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29150451 250000000 3084206882867 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3998565281/5000000000 : ℝ)^35 ≤ (74846922034807/100000000000000 : ℝ)^27 := by
    have hnat : (3998565281 : ℕ)^35*100000000000000^27 ≤ 74846922034807^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3998565281 5000000000 74846922034807 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1387744131/5000000000 : ℝ)^35 ≤ (949233209221/5000000000000 : ℝ)^27 := by
    have hnat : (1387744131 : ℕ)^35*5000000000000^27 ≤ 949233209221^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387744131 5000000000 949233209221 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(29150451/250000000 : ℝ), (3998565281/5000000000 : ℝ), (-1387744131/5000000000 : ℝ)] ![(3084206882867/50000000000000 : ℝ), (74846922034807/100000000000000 : ℝ), (949233209221/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(29150451/250000000 : ℝ)|^35 ≤ (3084206882867/50000000000000 : ℝ)^27
        have hw : |(29150451/250000000 : ℝ)|=(29150451/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3998565281/5000000000 : ℝ)|^35 ≤ (74846922034807/100000000000000 : ℝ)^27
        have hw : |(3998565281/5000000000 : ℝ)|=(3998565281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1387744131/5000000000 : ℝ)|^35 ≤ (949233209221/5000000000000 : ℝ)^27
        have hw : |(-1387744131/5000000000 : ℝ)|=(1387744131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s0_19 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (651144757/2500000000 : ℝ)*x 0 + (3571140619/10000000000 : ℝ)*x 1 + (400675633/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (651144757/2500000000 : ℝ)^35 ≤ (1748327288097/10000000000000 : ℝ)^27 := by
    have hnat : (651144757 : ℕ)^35*10000000000000^27 ≤ 1748327288097^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651144757 2500000000 1748327288097 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3571140619/10000000000 : ℝ)^35 ≤ (13160588556839/50000000000000 : ℝ)^27 := by
    have hnat : (3571140619 : ℕ)^35*50000000000000^27 ≤ 13160588556839^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3571140619 10000000000 13160588556839 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400675633/625000000 : ℝ)^35 ≤ (28097774994329/50000000000000 : ℝ)^27 := by
    have hnat : (400675633 : ℕ)^35*50000000000000^27 ≤ 28097774994329^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400675633 625000000 28097774994329 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(651144757/2500000000 : ℝ), (3571140619/10000000000 : ℝ), (400675633/625000000 : ℝ)] ![(1748327288097/10000000000000 : ℝ), (13160588556839/50000000000000 : ℝ), (28097774994329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(651144757/2500000000 : ℝ)|^35 ≤ (1748327288097/10000000000000 : ℝ)^27
        have hw : |(651144757/2500000000 : ℝ)|=(651144757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3571140619/10000000000 : ℝ)|^35 ≤ (13160588556839/50000000000000 : ℝ)^27
        have hw : |(3571140619/10000000000 : ℝ)|=(3571140619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(400675633/625000000 : ℝ)|^35 ≤ (28097774994329/50000000000000 : ℝ)^27
        have hw : |(400675633/625000000 : ℝ)|=(400675633/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s0_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-372827663/1250000000 : ℝ)*x 0 + (3931018731/10000000000 : ℝ)*x 1 + (2899720829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (372827663/1250000000 : ℝ)^35 ≤ (20841236561777/100000000000000 : ℝ)^27 := by
    have hnat : (372827663 : ℕ)^35*100000000000000^27 ≤ 20841236561777^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372827663 1250000000 20841236561777 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3931018731/10000000000 : ℝ)^35 ≤ (14904880019283/50000000000000 : ℝ)^27 := by
    have hnat : (3931018731 : ℕ)^35*50000000000000^27 ≤ 14904880019283^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3931018731 10000000000 14904880019283 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2899720829/5000000000 : ℝ)^35 ≤ (24674501693513/50000000000000 : ℝ)^27 := by
    have hnat : (2899720829 : ℕ)^35*50000000000000^27 ≤ 24674501693513^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2899720829 5000000000 24674501693513 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-372827663/1250000000 : ℝ), (3931018731/10000000000 : ℝ), (2899720829/5000000000 : ℝ)] ![(20841236561777/100000000000000 : ℝ), (14904880019283/50000000000000 : ℝ), (24674501693513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-372827663/1250000000 : ℝ)|^35 ≤ (20841236561777/100000000000000 : ℝ)^27
        have hw : |(-372827663/1250000000 : ℝ)|=(372827663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3931018731/10000000000 : ℝ)|^35 ≤ (14904880019283/50000000000000 : ℝ)^27
        have hw : |(3931018731/10000000000 : ℝ)|=(3931018731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2899720829/5000000000 : ℝ)|^35 ≤ (24674501693513/50000000000000 : ℝ)^27
        have hw : |(2899720829/5000000000 : ℝ)|=(2899720829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s0_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7886017119/10000000000 : ℝ)*x 0 + (-24151351/1000000000 : ℝ)*x 1 + (3505635633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7886017119/10000000000 : ℝ)^35 ≤ (73501641567749/100000000000000 : ℝ)^27 := by
    have hnat : (7886017119 : ℕ)^35*100000000000000^27 ≤ 73501641567749^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7886017119 10000000000 73501641567749 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24151351/1000000000 : ℝ)^35 ≤ (50083305177/6250000000000 : ℝ)^27 := by
    have hnat : (24151351 : ℕ)^35*6250000000000^27 ≤ 50083305177^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24151351 1000000000 50083305177 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3505635633/10000000000 : ℝ)^35 ≤ (25697025530019/100000000000000 : ℝ)^27 := by
    have hnat : (3505635633 : ℕ)^35*100000000000000^27 ≤ 25697025530019^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3505635633 10000000000 25697025530019 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7886017119/10000000000 : ℝ), (-24151351/1000000000 : ℝ), (3505635633/10000000000 : ℝ)] ![(73501641567749/100000000000000 : ℝ), (50083305177/6250000000000 : ℝ), (25697025530019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7886017119/10000000000 : ℝ)|^35 ≤ (73501641567749/100000000000000 : ℝ)^27
        have hw : |(7886017119/10000000000 : ℝ)|=(7886017119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24151351/1000000000 : ℝ)|^35 ≤ (50083305177/6250000000000 : ℝ)^27
        have hw : |(-24151351/1000000000 : ℝ)|=(24151351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3505635633/10000000000 : ℝ)|^35 ≤ (25697025530019/100000000000000 : ℝ)^27
        have hw : |(3505635633/10000000000 : ℝ)|=(3505635633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s0_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (147708037/2500000000 : ℝ)*x 0 + (932932869/1000000000 : ℝ)*x 1 + (-45952821/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (147708037/2500000000 : ℝ)^35 ≤ (2555368200833/100000000000000 : ℝ)^27 := by
    have hnat : (147708037 : ℕ)^35*100000000000000^27 ≤ 2555368200833^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147708037 2500000000 2555368200833 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (932932869/1000000000 : ℝ)^35 ≤ (91393893214977/100000000000000 : ℝ)^27 := by
    have hnat : (932932869 : ℕ)^35*100000000000000^27 ≤ 91393893214977^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932932869 1000000000 91393893214977 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45952821/400000000 : ℝ)^35 ≤ (3025369287481/50000000000000 : ℝ)^27 := by
    have hnat : (45952821 : ℕ)^35*50000000000000^27 ≤ 3025369287481^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45952821 400000000 3025369287481 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(147708037/2500000000 : ℝ), (932932869/1000000000 : ℝ), (-45952821/400000000 : ℝ)] ![(2555368200833/100000000000000 : ℝ), (91393893214977/100000000000000 : ℝ), (3025369287481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(147708037/2500000000 : ℝ)|^35 ≤ (2555368200833/100000000000000 : ℝ)^27
        have hw : |(147708037/2500000000 : ℝ)|=(147708037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(932932869/1000000000 : ℝ)|^35 ≤ (91393893214977/100000000000000 : ℝ)^27
        have hw : |(932932869/1000000000 : ℝ)|=(932932869/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45952821/400000000 : ℝ)|^35 ≤ (3025369287481/50000000000000 : ℝ)^27
        have hw : |(-45952821/400000000 : ℝ)|=(45952821/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s0_25 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6885169541/10000000000 : ℝ)*x 0 + (2526257599/10000000000 : ℝ)*x 1 + (3060720681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6885169541/10000000000 : ℝ)^35 ≤ (30821896018643/50000000000000 : ℝ)^27 := by
    have hnat : (6885169541 : ℕ)^35*50000000000000^27 ≤ 30821896018643^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6885169541 10000000000 30821896018643 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2526257599/10000000000 : ℝ)^35 ≤ (1680482400667/10000000000000 : ℝ)^27 := by
    have hnat : (2526257599 : ℕ)^35*10000000000000^27 ≤ 1680482400667^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2526257599 10000000000 1680482400667 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3060720681/10000000000 : ℝ)^35 ≤ (21551383946797/100000000000000 : ℝ)^27 := by
    have hnat : (3060720681 : ℕ)^35*100000000000000^27 ≤ 21551383946797^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3060720681 10000000000 21551383946797 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6885169541/10000000000 : ℝ), (2526257599/10000000000 : ℝ), (3060720681/10000000000 : ℝ)] ![(30821896018643/50000000000000 : ℝ), (1680482400667/10000000000000 : ℝ), (21551383946797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6885169541/10000000000 : ℝ)|^35 ≤ (30821896018643/50000000000000 : ℝ)^27
        have hw : |(6885169541/10000000000 : ℝ)|=(6885169541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2526257599/10000000000 : ℝ)|^35 ≤ (1680482400667/10000000000000 : ℝ)^27
        have hw : |(2526257599/10000000000 : ℝ)|=(2526257599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3060720681/10000000000 : ℝ)|^35 ≤ (21551383946797/100000000000000 : ℝ)^27
        have hw : |(3060720681/10000000000 : ℝ)|=(3060720681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2034239641/5000000000 : ℝ)*x 0 + (4258777263/10000000000 : ℝ)*x 1 + (282729213/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2034239641/5000000000 : ℝ)^35 ≤ (97399855109/312500000000 : ℝ)^27 := by
    have hnat : (2034239641 : ℕ)^35*312500000000^27 ≤ 97399855109^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034239641 5000000000 97399855109 312500000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4258777263/10000000000 : ℝ)^35 ≤ (33070702738383/100000000000000 : ℝ)^27 := by
    have hnat : (4258777263 : ℕ)^35*100000000000000^27 ≤ 33070702738383^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258777263 10000000000 33070702738383 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282729213/625000000 : ℝ)^35 ≤ (8940335901809/25000000000000 : ℝ)^27 := by
    have hnat : (282729213 : ℕ)^35*25000000000000^27 ≤ 8940335901809^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282729213 625000000 8940335901809 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2034239641/5000000000 : ℝ), (4258777263/10000000000 : ℝ), (282729213/625000000 : ℝ)] ![(97399855109/312500000000 : ℝ), (33070702738383/100000000000000 : ℝ), (8940335901809/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2034239641/5000000000 : ℝ)|^35 ≤ (97399855109/312500000000 : ℝ)^27
        have hw : |(-2034239641/5000000000 : ℝ)|=(2034239641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4258777263/10000000000 : ℝ)|^35 ≤ (33070702738383/100000000000000 : ℝ)^27
        have hw : |(4258777263/10000000000 : ℝ)|=(4258777263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282729213/625000000 : ℝ)|^35 ≤ (8940335901809/25000000000000 : ℝ)^27
        have hw : |(282729213/625000000 : ℝ)|=(282729213/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1086544993/2000000000 : ℝ)*x 0 + (-2354423811/10000000000 : ℝ)*x 1 + (1216767561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086544993/2000000000 : ℝ)^35 ≤ (1813695778293/4000000000000 : ℝ)^27 := by
    have hnat : (1086544993 : ℕ)^35*4000000000000^27 ≤ 1813695778293^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086544993 2000000000 1813695778293 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2354423811/10000000000 : ℝ)^35 ≤ (15338270297599/100000000000000 : ℝ)^27 := by
    have hnat : (2354423811 : ℕ)^35*100000000000000^27 ≤ 15338270297599^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2354423811 10000000000 15338270297599 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1216767561/2500000000 : ℝ)^35 ≤ (4914916903591/12500000000000 : ℝ)^27 := by
    have hnat : (1216767561 : ℕ)^35*12500000000000^27 ≤ 4914916903591^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216767561 2500000000 4914916903591 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086544993/2000000000 : ℝ), (-2354423811/10000000000 : ℝ), (1216767561/2500000000 : ℝ)] ![(1813695778293/4000000000000 : ℝ), (15338270297599/100000000000000 : ℝ), (4914916903591/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086544993/2000000000 : ℝ)|^35 ≤ (1813695778293/4000000000000 : ℝ)^27
        have hw : |(1086544993/2000000000 : ℝ)|=(1086544993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2354423811/10000000000 : ℝ)|^35 ≤ (15338270297599/100000000000000 : ℝ)^27
        have hw : |(-2354423811/10000000000 : ℝ)|=(2354423811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1216767561/2500000000 : ℝ)|^35 ≤ (4914916903591/12500000000000 : ℝ)^27
        have hw : |(1216767561/2500000000 : ℝ)|=(1216767561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3031346967/10000000000 : ℝ)*x 0 + (624298579/1000000000 : ℝ)*x 1 + (-421312379/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3031346967/10000000000 : ℝ)^35 ≤ (10641827508671/50000000000000 : ℝ)^27 := by
    have hnat : (3031346967 : ℕ)^35*50000000000000^27 ≤ 10641827508671^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3031346967 10000000000 10641827508671 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624298579/1000000000 : ℝ)^35 ≤ (6787000316857/12500000000000 : ℝ)^27 := by
    have hnat : (624298579 : ℕ)^35*12500000000000^27 ≤ 6787000316857^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624298579 1000000000 6787000316857 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421312379/1250000000 : ℝ)^35 ≤ (12210171215443/50000000000000 : ℝ)^27 := by
    have hnat : (421312379 : ℕ)^35*50000000000000^27 ≤ 12210171215443^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421312379 1250000000 12210171215443 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3031346967/10000000000 : ℝ), (624298579/1000000000 : ℝ), (-421312379/1250000000 : ℝ)] ![(10641827508671/50000000000000 : ℝ), (6787000316857/12500000000000 : ℝ), (12210171215443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3031346967/10000000000 : ℝ)|^35 ≤ (10641827508671/50000000000000 : ℝ)^27
        have hw : |(3031346967/10000000000 : ℝ)|=(3031346967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(624298579/1000000000 : ℝ)|^35 ≤ (6787000316857/12500000000000 : ℝ)^27
        have hw : |(624298579/1000000000 : ℝ)|=(624298579/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-421312379/1250000000 : ℝ)|^35 ≤ (12210171215443/50000000000000 : ℝ)^27
        have hw : |(-421312379/1250000000 : ℝ)|=(421312379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308029_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4673741331/10000000000 : ℝ)*x 0 + (996266399/2500000000 : ℝ)*x 1 + (2093555951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4673741331/10000000000 : ℝ)^35 ≤ (7461352091171/20000000000000 : ℝ)^27 := by
    have hnat : (4673741331 : ℕ)^35*20000000000000^27 ≤ 7461352091171^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4673741331 10000000000 7461352091171 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (996266399/2500000000 : ℝ)^35 ≤ (30342124458973/100000000000000 : ℝ)^27 := by
    have hnat : (996266399 : ℕ)^35*100000000000000^27 ≤ 30342124458973^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996266399 2500000000 30342124458973 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2093555951/5000000000 : ℝ)^35 ≤ (8087778768081/25000000000000 : ℝ)^27 := by
    have hnat : (2093555951 : ℕ)^35*25000000000000^27 ≤ 8087778768081^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093555951 5000000000 8087778768081 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4673741331/10000000000 : ℝ), (996266399/2500000000 : ℝ), (2093555951/5000000000 : ℝ)] ![(7461352091171/20000000000000 : ℝ), (30342124458973/100000000000000 : ℝ), (8087778768081/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4673741331/10000000000 : ℝ)|^35 ≤ (7461352091171/20000000000000 : ℝ)^27
        have hw : |(4673741331/10000000000 : ℝ)|=(4673741331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(996266399/2500000000 : ℝ)|^35 ≤ (30342124458973/100000000000000 : ℝ)^27
        have hw : |(996266399/2500000000 : ℝ)|=(996266399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2093555951/5000000000 : ℝ)|^35 ≤ (8087778768081/25000000000000 : ℝ)^27
        have hw : |(2093555951/5000000000 : ℝ)|=(2093555951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308029 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3993742303/10000000000 : ℝ)*X 0 0+(60527131/156250000 : ℝ)*X 0 1+(198510347/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((6134044837/10000000000 : ℝ)*X 1 0+(-1025191739/10000000000 : ℝ)*X 1 1+(2546834221/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((956262057/5000000000 : ℝ)*X 2 0+(3912251201/5000000000 : ℝ)*X 2 1+(-2376566869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_4 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2092732173/5000000000 : ℝ)*X 0 0+(2850384109/10000000000 : ℝ)*X 0 1+(1419508701/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1376538279/2500000000 : ℝ)*X 1 0+(-51447047/2000000000 : ℝ)*X 1 1+(6127000869/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((294669163/5000000000 : ℝ)*X 2 0+(4754066023/5000000000 : ℝ)*X 2 1+(-799501143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((498913079/1250000000 : ℝ)*X 0 0+(1104352797/2500000000 : ℝ)*X 0 1+(4441345243/10000000000 : ℝ)*X 0 2+(498913079/1250000000 : ℝ)*X 1 0+(1104352797/2500000000 : ℝ)*X 1 1+(4441345243/10000000000 : ℝ)*X 1 2+(498913079/1250000000 : ℝ)*X 2 0+(1104352797/2500000000 : ℝ)*X 2 1+(4441345243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-4876010521/10000000000 : ℝ)*X 0 0+(1224619621/5000000000 : ℝ)*X 0 1+(5349432663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((1829097901/2500000000 : ℝ)*X 1 0+(-1216443883/10000000000 : ℝ)*X 1 1+(362003799/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((29150451/250000000 : ℝ)*X 2 0+(3998565281/5000000000 : ℝ)*X 2 1+(-1387744131/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((651144757/2500000000 : ℝ)*X 0 0+(3571140619/10000000000 : ℝ)*X 0 1+(400675633/625000000 : ℝ)*X 0 2+(651144757/2500000000 : ℝ)*X 1 0+(3571140619/10000000000 : ℝ)*X 1 1+(400675633/625000000 : ℝ)*X 1 2+(651144757/2500000000 : ℝ)*X 2 0+(3571140619/10000000000 : ℝ)*X 2 1+(400675633/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-372827663/1250000000 : ℝ)*X 0 0+(3931018731/10000000000 : ℝ)*X 0 1+(2899720829/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((7886017119/10000000000 : ℝ)*X 1 0+(-24151351/1000000000 : ℝ)*X 1 1+(3505635633/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((147708037/2500000000 : ℝ)*X 2 0+(932932869/1000000000 : ℝ)*X 2 1+(-45952821/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((6885169541/10000000000 : ℝ)*X 0 0+(2526257599/10000000000 : ℝ)*X 0 1+(3060720681/10000000000 : ℝ)*X 0 2+(6885169541/10000000000 : ℝ)*X 1 0+(2526257599/10000000000 : ℝ)*X 1 1+(3060720681/10000000000 : ℝ)*X 1 2+(6885169541/10000000000 : ℝ)*X 2 0+(2526257599/10000000000 : ℝ)*X 2 1+(3060720681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((21593/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21593/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13880533296485207351121/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40708018841/100000000000 : ℝ)*(base50) + (530715927253/1000000000000 : ℝ)*(base59) + (2502332267783/1000000000000 : ℝ)*(major_s0_0) + (4658458726561/1000000000000 : ℝ)*(major_s0_1) + (2502332267783/1000000000000 : ℝ)*(major_s0_2) + (16614823/125000000000 : ℝ)*(sp_s0_0) + (1078063229389/500000000000 : ℝ)*(sp_s0_4) + (851935703771/250000000000 : ℝ)*(sp_s0_7) + (425984800187/125000000000 : ℝ)*(sp_s0_8) + (3407517789929/1000000000000 : ℝ)*(sp_s0_9) + (1596766980493/1000000000000 : ℝ)*(sp_s0_12) + (666957/250000000000 : ℝ)*(sp_s0_13) + (14526729/1000000000000 : ℝ)*(sp_s0_19) + (360611567/1000000000000 : ℝ)*(sp_s0_22) + (798390753611/500000000000 : ℝ)*(f.failure) + (425984800187/125000000000 : ℝ)*(f.sum) + (105629829777147/5000000000000000000000000000 : ℝ)*base63 + (285688500128029/1250000000000000000000000000 : ℝ)*base64 + (500485237270757/1250000000000000000000000000 : ℝ)*base66 + (2733033642915409/10000000000000000000000000000 : ℝ)*base68 + (69618771939641/10000000000000000000000000000 : ℝ)*base70 + (322984482121971/1250000000000000000000000000 : ℝ)*base72 + (3044198395530297/10000000000000000000000000000 : ℝ)*base74 + (4099172017915409/10000000000000000000000000000 : ℝ)*base76 + (537768735483/78125000000000000000000000 : ℝ)*base78 + (16579/50000000000000000 : ℝ)*base86 + (16579/50000000000000000 : ℝ)*base88 + (16579/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18883/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(18883/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (47969683761239627198601/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15246901723/250000000000 : ℝ)*(base3) + (443485454063/1000000000000 : ℝ)*(base40) + (4360543/1000000000000 : ℝ)*(base54) + (466938738701/1000000000000 : ℝ)*(base59) + (988361018913/500000000000 : ℝ)*(major_s0_0) + (988361018913/500000000000 : ℝ)*(major_s0_1) + (1976717677283/1000000000000 : ℝ)*(major_s0_2) + (6609001/1000000000000 : ℝ)*(sp_s0_1) + (40084699/1000000000000 : ℝ)*(sp_s0_2) + (673015087641/250000000000 : ℝ)*(sp_s0_13) + (1376490499741/500000000000 : ℝ)*(sp_s0_14) + (1346007952661/500000000000 : ℝ)*(sp_s0_15) + (1200388559667/1000000000000 : ℝ)*(sp_s0_19) + (30174487/500000000000 : ℝ)*(sp_s0_21) + (630690263551/500000000000 : ℝ)*(f.failure) + (673015087641/250000000000 : ℝ)*(f.sum) + (543556569143111/10000000000000000000000000000 : ℝ)*base62 + (995265806226529/1250000000000000000000000000 : ℝ)*base64 + (435259818078781/625000000000000000000000000 : ℝ)*base66 + (11984277502933909/10000000000000000000000000000 : ℝ)*base68 + (572296809560303/1000000000000000000000000000 : ℝ)*base70 + (573665207578781/625000000000000000000000000 : ℝ)*base72 + (1681690011604601/5000000000000000000000000000 : ℝ)*base74 + (3128918026895399/5000000000000000000000000000 : ℝ)*base76 + (21771723235031/312500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (40761/50000000000000000 : ℝ)*base87 + (40761/50000000000000000 : ℝ)*base89 + (40761/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7083/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7083/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1351722250430000352309/100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37865943411/50000000000 : ℝ)*(base40) + (128425858751/500000000000 : ℝ)*(base50) + (110415305541/200000000000 : ℝ)*(base59) + (2974523396831/1000000000000 : ℝ)*(major_s0_0) + (66129262449/10000000000 : ℝ)*(major_s0_1) + (2974523396831/1000000000000 : ℝ)*(major_s0_2) + (89109613/1000000000000 : ℝ)*(sp_s0_0) + (3638402848069/1000000000000 : ℝ)*(sp_s0_4) + (36761339/500000000000 : ℝ)*(sp_s0_14) + (643649/200000000000 : ℝ)*(sp_s0_15) + (126589323229/31250000000 : ℝ)*(sp_s0_20) + (4050873930263/1000000000000 : ℝ)*(sp_s0_21) + (506368029337/125000000000 : ℝ)*(sp_s0_22) + (189809483497/100000000000 : ℝ)*(sp_s0_25) + (189809483497/100000000000 : ℝ)*(f.failure) + (4050947452941/1000000000000 : ℝ)*(f.sum) + (280128107750787/10000000000000000000000000000 : ℝ)*base63 + (292060178855747/1250000000000000000000000000 : ℝ)*base65 + (5160134011137/12500000000000000000000000 : ℝ)*base67 + (9634326689198087/10000000000000000000000000000 : ℝ)*base69 + (2955792663044063/10000000000000000000000000000 : ℝ)*base71 + (229191513769253/1250000000000000000000000000 : ℝ)*base73 + (42651195805527/100000000000000000000000000 : ℝ)*base75 + (12807774308198087/10000000000000000000000000000 : ℝ)*base77 + (655758902867047/1250000000000000000000000000 : ℝ)*base78 + (11633/10000000000000000 : ℝ)*base86 + (11633/10000000000000000 : ℝ)*base88 + (11633/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (21593/50000 : ℝ) ^ (17/4 : ℝ) ≤ (2819730921000286863/100000000000000000000 : ℝ) := by
    have hpowers : (21593/50000 : ℝ)^17 ≤ (2819730921000286863/100000000000000000000 : ℝ)^4 := by
      have hnat : (21593 : ℕ)^17*100000000000000000000^4 ≤ 2819730921000286863^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21593 50000 2819730921000286863 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21593/50000 : ℝ)) (X := (2819730921000286863/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (102819730921000286863/100000000000000000000 : ℝ) ≤ (5032821471837787/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (102819730921000286863/100000000000000000000 : ℝ)^4 ≤ (5032821471837787/5000000000000000 : ℝ)^17 := by
      have hnat : (102819730921000286863 : ℕ)^4*5000000000000000^17 ≤ 5032821471837787^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102819730921000286863 100000000000000000000 5032821471837787 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5032821471837787/5000000000000000 : ℝ)) (X := (102819730921000286863/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (52819730921000286863/50000000000000000000 : ℝ) ≤ (2025984673859697/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (52819730921000286863/50000000000000000000 : ℝ)^4 ≤ (2025984673859697/2000000000000000 : ℝ)^17 := by
      have hnat : (52819730921000286863 : ℕ)^4*2000000000000000^17 ≤ 2025984673859697^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52819730921000286863 50000000000000000000 2025984673859697 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2025984673859697/2000000000000000 : ℝ)) (X := (52819730921000286863/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(32821471837787/2159300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(64280425622911/4318600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (21593/50000 : ℝ)) (alpha := (32821471837787/2159300000000000 : ℝ)) (beta := (64280425622911/4318600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (21593/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(32821471837787/2159300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(64280425622911/4318600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (18883/100000 : ℝ) ^ (17/4 : ℝ) ≤ (83811134762199159/100000000000000000000 : ℝ) := by
    have hpowers : (18883/100000 : ℝ)^17 ≤ (83811134762199159/100000000000000000000 : ℝ)^4 := by
      have hnat : (18883 : ℕ)^17*100000000000000000000^4 ≤ 83811134762199159^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18883 100000 83811134762199159 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18883/100000 : ℝ)) (X := (83811134762199159/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100083811134762199159/100000000000000000000 : ℝ) ≤ (2500492848766787/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100083811134762199159/100000000000000000000 : ℝ)^4 ≤ (2500492848766787/2500000000000000 : ℝ)^17 := by
      have hnat : (100083811134762199159 : ℕ)^4*2500000000000000^17 ≤ 2500492848766787^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100083811134762199159 100000000000000000000 2500492848766787 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500492848766787/2500000000000000 : ℝ)) (X := (100083811134762199159/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50083811134762199159/50000000000000000000 : ℝ) ≤ (156311586376751/156250000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50083811134762199159/50000000000000000000 : ℝ)^4 ≤ (156311586376751/156250000000000 : ℝ)^17 := by
      have hnat : (50083811134762199159 : ℕ)^4*156250000000000^17 ≤ 156311586376751^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50083811134762199159 50000000000000000000 156311586376751 156250000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156311586376751/156250000000000 : ℝ)) (X := (50083811134762199159/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(492848766787/472075000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(492533261229/472075000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (18883/100000 : ℝ)) (alpha := (492848766787/472075000000000 : ℝ)) (beta := (492533261229/472075000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (18883/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(492848766787/472075000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(492533261229/472075000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (7083/12500 : ℝ) ^ (17/4 : ℝ) ≤ (894449287309398803/10000000000000000000 : ℝ) := by
    have hpowers : (7083/12500 : ℝ)^17 ≤ (894449287309398803/10000000000000000000 : ℝ)^4 := by
      have hnat : (7083 : ℕ)^17*10000000000000000000^4 ≤ 894449287309398803^4*12500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7083 12500 894449287309398803 10000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7083/12500 : ℝ)) (X := (894449287309398803/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (10894449287309398803/10000000000000000000 : ℝ) ≤ (10203617827440461/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (10894449287309398803/10000000000000000000 : ℝ)^4 ≤ (10203617827440461/10000000000000000 : ℝ)^17 := by
      have hnat : (10894449287309398803 : ℕ)^4*10000000000000000^17 ≤ 10203617827440461^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10894449287309398803 10000000000000000000 10203617827440461 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10203617827440461/10000000000000000 : ℝ)) (X := (10894449287309398803/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (5894449287309398803/5000000000000000000 : ℝ) ≤ (2598706541035947/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (5894449287309398803/5000000000000000000 : ℝ)^4 ≤ (2598706541035947/2500000000000000 : ℝ)^17 := by
      have hnat : (5894449287309398803 : ℕ)^4*2500000000000000^17 ≤ 2598706541035947^17*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5894449287309398803 5000000000000000000 2598706541035947 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2598706541035947/2500000000000000 : ℝ)) (X := (5894449287309398803/5000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(203617827440461/5666400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(191208336703327/5666400000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (7083/12500 : ℝ)) (alpha := (203617827440461/5666400000000000 : ℝ)) (beta := (191208336703327/5666400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (7083/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(203617827440461/5666400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(191208336703327/5666400000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2034239641/5000000000 : ℝ)*X 0 0+(4258777263/10000000000 : ℝ)*X 0 1+(282729213/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1086544993/2000000000 : ℝ)*X 1 0+(-2354423811/10000000000 : ℝ)*X 1 1+(1216767561/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3031346967/10000000000 : ℝ)*X 2 0+(624298579/1000000000 : ℝ)*X 2 1+(-421312379/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4673741331/10000000000 : ℝ)*X 0 0+(996266399/2500000000 : ℝ)*X 0 1+(2093555951/5000000000 : ℝ)*X 0 2+(4673741331/10000000000 : ℝ)*X 1 0+(996266399/2500000000 : ℝ)*X 1 1+(2093555951/5000000000 : ℝ)*X 1 2+(4673741331/10000000000 : ℝ)*X 2 0+(996266399/2500000000 : ℝ)*X 2 1+(2093555951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308029_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-320133/50000 : ℝ) < ((-156711/100000 : ℝ)*P 0+(-156711/100000 : ℝ)*P 1+(-156711/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-320133/50000 : ℝ) < (-20485114904199575885389597844068067/3208918671530000000000000000000000 : ℝ) := by norm_num
    linear_combination (4457/100000000000 : ℝ)*(base3) + (5993/500000000000 : ℝ)*(base11) + (169169/1000000000000 : ℝ)*(base13) + (68021717339/500000000000 : ℝ)*(base40) + (66405549241/250000000000 : ℝ)*(base49) + (453048764829/1000000000000 : ℝ)*(base50) + (209482304667/1000000000000 : ℝ)*(base59) + (369/50000000000 : ℝ)*(ratio_s0_2) + (156711/100000 : ℝ)*(major_s1_0) + (156711/100000 : ℝ)*(major_s1_1) + (156711/100000 : ℝ)*(major_s1_2) + (4156123473/1953125000 : ℝ)*(sp_s1_0) + (2127935443901/1000000000000 : ℝ)*(sp_s1_1) + (2127935399331/1000000000000 : ℝ)*(sp_s1_2) + (99999995543/100000000000 : ℝ)*(sp_s1_6) + (2127935399331/1000000000000 : ℝ)*(f.sum) + (31726662467127287/222913815000000000000000000000 : ℝ)*base62 + (125844888391/184453125000000000000000 : ℝ)*base64 + (3573595554711/47207500000000000000000000 : ℝ)*base66 + (12334656601/4722000000000000000000000 : ℝ)*base69 + (450881984153512537/509810730000000000000000000000 : ℝ)*base70 + (9069945407691/26991250000000000000000000 : ℝ)*base73 + (62020581633381/188830000000000000000000000 : ℝ)*base74 + (11484588258261/21593000000000000000000000 : ℝ)*base76 + (230332239637248527/1019351547500000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p008_b018 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 29 ≤ c.val) (hhi : c.val < 30)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=29 := by omega
  rcases hc with rfl
  · exact collision_c308029 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 29 ≤ c.val) (hhi : c.val < 30)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p008_b018 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

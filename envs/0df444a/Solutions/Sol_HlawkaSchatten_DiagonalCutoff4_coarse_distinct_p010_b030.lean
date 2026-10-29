-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b030
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:16:34.651068+00:00
-- url     : https://prove2.me/submissions/74f932f6-b710-42c8-9f34-e6b263f5639a

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
theorem collision_support_c310068_s0_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7636715371/10000000000 : ℝ)*x 0 + (714880383/2500000000 : ℝ)*x 1 + (-809142993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7636715371/10000000000 : ℝ)^71 ≤ (70606237782783/100000000000000 : ℝ)^55 := by
    have hnat : (7636715371 : ℕ)^71*100000000000000^55 ≤ 70606237782783^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7636715371 10000000000 70606237782783 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (714880383/2500000000 : ℝ)^71 ≤ (9933314233757/50000000000000 : ℝ)^55 := by
    have hnat : (714880383 : ℕ)^71*50000000000000^55 ≤ 9933314233757^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714880383 2500000000 9933314233757 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (809142993/5000000000 : ℝ)^71 ≤ (381085349629/4000000000000 : ℝ)^55 := by
    have hnat : (809142993 : ℕ)^71*4000000000000^55 ≤ 381085349629^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809142993 5000000000 381085349629 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7636715371/10000000000 : ℝ), (714880383/2500000000 : ℝ), (-809142993/5000000000 : ℝ)] ![(70606237782783/100000000000000 : ℝ), (9933314233757/50000000000000 : ℝ), (381085349629/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7636715371/10000000000 : ℝ)|^71 ≤ (70606237782783/100000000000000 : ℝ)^55
        have hw : |(7636715371/10000000000 : ℝ)|=(7636715371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(714880383/2500000000 : ℝ)|^71 ≤ (9933314233757/50000000000000 : ℝ)^55
        have hw : |(714880383/2500000000 : ℝ)|=(714880383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-809142993/5000000000 : ℝ)|^71 ≤ (381085349629/4000000000000 : ℝ)^55
        have hw : |(-809142993/5000000000 : ℝ)|=(809142993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s0_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-243220073/5000000000 : ℝ)*x 0 + (-1412115377/2500000000 : ℝ)*x 1 + (-5858370687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (243220073/5000000000 : ℝ)^71 ≤ (2018711836501/100000000000000 : ℝ)^55 := by
    have hnat : (243220073 : ℕ)^71*100000000000000^55 ≤ 2018711836501^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243220073 5000000000 2018711836501 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1412115377/2500000000 : ℝ)^71 ≤ (47837051761823/100000000000000 : ℝ)^55 := by
    have hnat : (1412115377 : ℕ)^71*100000000000000^55 ≤ 47837051761823^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1412115377 2500000000 47837051761823 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5858370687/10000000000 : ℝ)^71 ≤ (50144236383129/100000000000000 : ℝ)^55 := by
    have hnat : (5858370687 : ℕ)^71*100000000000000^55 ≤ 50144236383129^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5858370687 10000000000 50144236383129 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-243220073/5000000000 : ℝ), (-1412115377/2500000000 : ℝ), (-5858370687/10000000000 : ℝ)] ![(2018711836501/100000000000000 : ℝ), (47837051761823/100000000000000 : ℝ), (50144236383129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-243220073/5000000000 : ℝ)|^71 ≤ (2018711836501/100000000000000 : ℝ)^55
        have hw : |(-243220073/5000000000 : ℝ)|=(243220073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1412115377/2500000000 : ℝ)|^71 ≤ (47837051761823/100000000000000 : ℝ)^55
        have hw : |(-1412115377/2500000000 : ℝ)|=(1412115377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5858370687/10000000000 : ℝ)|^71 ≤ (50144236383129/100000000000000 : ℝ)^55
        have hw : |(-5858370687/10000000000 : ℝ)|=(5858370687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s0_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (953912947/1250000000 : ℝ)*x 0 + (1737061373/5000000000 : ℝ)*x 1 + (-812620349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (953912947/1250000000 : ℝ)^71 ≤ (7054165322543/10000000000000 : ℝ)^55 := by
    have hnat : (953912947 : ℕ)^71*10000000000000^55 ≤ 7054165322543^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953912947 1250000000 7054165322543 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1737061373/5000000000 : ℝ)^71 ≤ (25543055156851/100000000000000 : ℝ)^55 := by
    have hnat : (1737061373 : ℕ)^71*100000000000000^55 ≤ 25543055156851^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737061373 5000000000 25543055156851 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (812620349/10000000000 : ℝ)^71 ≤ (1957645802893/50000000000000 : ℝ)^55 := by
    have hnat : (812620349 : ℕ)^71*50000000000000^55 ≤ 1957645802893^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      812620349 10000000000 1957645802893 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(953912947/1250000000 : ℝ), (1737061373/5000000000 : ℝ), (-812620349/10000000000 : ℝ)] ![(7054165322543/10000000000000 : ℝ), (25543055156851/100000000000000 : ℝ), (1957645802893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(953912947/1250000000 : ℝ)|^71 ≤ (7054165322543/10000000000000 : ℝ)^55
        have hw : |(953912947/1250000000 : ℝ)|=(953912947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1737061373/5000000000 : ℝ)|^71 ≤ (25543055156851/100000000000000 : ℝ)^55
        have hw : |(1737061373/5000000000 : ℝ)|=(1737061373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-812620349/10000000000 : ℝ)|^71 ≤ (1957645802893/50000000000000 : ℝ)^55
        have hw : |(-812620349/10000000000 : ℝ)|=(812620349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s0_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (918591049/2000000000 : ℝ)*x 0 + (-1469408237/5000000000 : ℝ)*x 1 + (2590687001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (918591049/2000000000 : ℝ)^71 ≤ (36626191905277/100000000000000 : ℝ)^55 := by
    have hnat : (918591049 : ℕ)^71*100000000000000^55 ≤ 36626191905277^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918591049 2000000000 36626191905277 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1469408237/5000000000 : ℝ)^71 ≤ (1029032296617/5000000000000 : ℝ)^55 := by
    have hnat : (1469408237 : ℕ)^71*5000000000000^55 ≤ 1029032296617^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1469408237 5000000000 1029032296617 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590687001/5000000000 : ℝ)^71 ≤ (21396581069999/50000000000000 : ℝ)^55 := by
    have hnat : (2590687001 : ℕ)^71*50000000000000^55 ≤ 21396581069999^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590687001 5000000000 21396581069999 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(918591049/2000000000 : ℝ), (-1469408237/5000000000 : ℝ), (2590687001/5000000000 : ℝ)] ![(36626191905277/100000000000000 : ℝ), (1029032296617/5000000000000 : ℝ), (21396581069999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(918591049/2000000000 : ℝ)|^71 ≤ (36626191905277/100000000000000 : ℝ)^55
        have hw : |(918591049/2000000000 : ℝ)|=(918591049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1469408237/5000000000 : ℝ)|^71 ≤ (1029032296617/5000000000000 : ℝ)^55
        have hw : |(-1469408237/5000000000 : ℝ)|=(1469408237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590687001/5000000000 : ℝ)|^71 ≤ (21396581069999/50000000000000 : ℝ)^55
        have hw : |(2590687001/5000000000 : ℝ)|=(2590687001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s0_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (128834799/250000000 : ℝ)*x 0 + (-1325138831/10000000000 : ℝ)*x 1 + (-5858370687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128834799/250000000 : ℝ)^71 ≤ (10623765397127/25000000000000 : ℝ)^55 := by
    have hnat : (128834799 : ℕ)^71*25000000000000^55 ≤ 10623765397127^55*250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128834799 250000000 10623765397127 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1325138831/10000000000 : ℝ)^71 ≤ (7360702017227/100000000000000 : ℝ)^55 := by
    have hnat : (1325138831 : ℕ)^71*100000000000000^55 ≤ 7360702017227^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325138831 10000000000 7360702017227 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5858370687/10000000000 : ℝ)^71 ≤ (50144236383129/100000000000000 : ℝ)^55 := by
    have hnat : (5858370687 : ℕ)^71*100000000000000^55 ≤ 50144236383129^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5858370687 10000000000 50144236383129 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(128834799/250000000 : ℝ), (-1325138831/10000000000 : ℝ), (-5858370687/10000000000 : ℝ)] ![(10623765397127/25000000000000 : ℝ), (7360702017227/100000000000000 : ℝ), (50144236383129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(128834799/250000000 : ℝ)|^71 ≤ (10623765397127/25000000000000 : ℝ)^55
        have hw : |(128834799/250000000 : ℝ)|=(128834799/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1325138831/10000000000 : ℝ)|^71 ≤ (7360702017227/100000000000000 : ℝ)^55
        have hw : |(-1325138831/10000000000 : ℝ)|=(1325138831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5858370687/10000000000 : ℝ)|^71 ≤ (50144236383129/100000000000000 : ℝ)^55
        have hw : |(-5858370687/10000000000 : ℝ)|=(5858370687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s0_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-166919767/10000000000 : ℝ)*x 0 + (-1058099841/2500000000 : ℝ)*x 1 + (-911664677/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166919767/10000000000 : ℝ)^71 ≤ (253740110917/50000000000000 : ℝ)^55 := by
    have hnat : (166919767 : ℕ)^71*50000000000000^55 ≤ 253740110917^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166919767 10000000000 253740110917 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058099841/2500000000 : ℝ)^71 ≤ (8239432650853/25000000000000 : ℝ)^55 := by
    have hnat : (1058099841 : ℕ)^71*25000000000000^55 ≤ 8239432650853^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058099841 2500000000 8239432650853 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (911664677/1250000000 : ℝ)^71 ≤ (66534789155501/100000000000000 : ℝ)^55 := by
    have hnat : (911664677 : ℕ)^71*100000000000000^55 ≤ 66534789155501^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911664677 1250000000 66534789155501 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-166919767/10000000000 : ℝ), (-1058099841/2500000000 : ℝ), (-911664677/1250000000 : ℝ)] ![(253740110917/50000000000000 : ℝ), (8239432650853/25000000000000 : ℝ), (66534789155501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-166919767/10000000000 : ℝ)|^71 ≤ (253740110917/50000000000000 : ℝ)^55
        have hw : |(-166919767/10000000000 : ℝ)|=(166919767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1058099841/2500000000 : ℝ)|^71 ≤ (8239432650853/25000000000000 : ℝ)^55
        have hw : |(-1058099841/2500000000 : ℝ)|=(1058099841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-911664677/1250000000 : ℝ)|^71 ≤ (66534789155501/100000000000000 : ℝ)^55
        have hw : |(-911664677/1250000000 : ℝ)|=(911664677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s0_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (454246527/500000000 : ℝ)*x 0 + (208994751/1250000000 : ℝ)*x 1 + (-214357687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (454246527/500000000 : ℝ)^71 ≤ (44174027107223/50000000000000 : ℝ)^55 := by
    have hnat : (454246527 : ℕ)^71*50000000000000^55 ≤ 44174027107223^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454246527 500000000 44174027107223 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208994751/1250000000 : ℝ)^71 ≤ (9936983370643/100000000000000 : ℝ)^55 := by
    have hnat : (208994751 : ℕ)^71*100000000000000^55 ≤ 9936983370643^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208994751 1250000000 9936983370643 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214357687/5000000000 : ℝ)^71 ≤ (857481198517/50000000000000 : ℝ)^55 := by
    have hnat : (214357687 : ℕ)^71*50000000000000^55 ≤ 857481198517^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214357687 5000000000 857481198517 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(454246527/500000000 : ℝ), (208994751/1250000000 : ℝ), (-214357687/5000000000 : ℝ)] ![(44174027107223/50000000000000 : ℝ), (9936983370643/100000000000000 : ℝ), (857481198517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(454246527/500000000 : ℝ)|^71 ≤ (44174027107223/50000000000000 : ℝ)^55
        have hw : |(454246527/500000000 : ℝ)|=(454246527/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208994751/1250000000 : ℝ)|^71 ≤ (9936983370643/100000000000000 : ℝ)^55
        have hw : |(208994751/1250000000 : ℝ)|=(208994751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214357687/5000000000 : ℝ)|^71 ≤ (857481198517/50000000000000 : ℝ)^55
        have hw : |(-214357687/5000000000 : ℝ)|=(214357687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s0_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4838191263/10000000000 : ℝ)*x 0 + (-2224441699/5000000000 : ℝ)*x 1 + (1744272529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4838191263/10000000000 : ℝ)^71 ≤ (19585040092949/50000000000000 : ℝ)^55 := by
    have hnat : (4838191263 : ℕ)^71*50000000000000^55 ≤ 19585040092949^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838191263 10000000000 19585040092949 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2224441699/5000000000 : ℝ)^71 ≤ (2196868519953/6250000000000 : ℝ)^55 := by
    have hnat : (2224441699 : ℕ)^71*6250000000000^55 ≤ 2196868519953^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224441699 5000000000 2196868519953 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1744272529/5000000000 : ℝ)^71 ≤ (12840011739201/50000000000000 : ℝ)^55 := by
    have hnat : (1744272529 : ℕ)^71*50000000000000^55 ≤ 12840011739201^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744272529 5000000000 12840011739201 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4838191263/10000000000 : ℝ), (-2224441699/5000000000 : ℝ), (1744272529/5000000000 : ℝ)] ![(19585040092949/50000000000000 : ℝ), (2196868519953/6250000000000 : ℝ), (12840011739201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4838191263/10000000000 : ℝ)|^71 ≤ (19585040092949/50000000000000 : ℝ)^55
        have hw : |(4838191263/10000000000 : ℝ)|=(4838191263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2224441699/5000000000 : ℝ)|^71 ≤ (2196868519953/6250000000000 : ℝ)^55
        have hw : |(-2224441699/5000000000 : ℝ)|=(2224441699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1744272529/5000000000 : ℝ)|^71 ≤ (12840011739201/50000000000000 : ℝ)^55
        have hw : |(1744272529/5000000000 : ℝ)|=(1744272529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s0_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1275239133/5000000000 : ℝ)*x 0 + (-2456119681/10000000000 : ℝ)*x 1 + (-911664677/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1275239133/5000000000 : ℝ)^71 ≤ (685586812683/4000000000000 : ℝ)^55 := by
    have hnat : (1275239133 : ℕ)^71*4000000000000^55 ≤ 685586812683^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275239133 5000000000 685586812683 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2456119681/10000000000 : ℝ)^71 ≤ (3265108101323/20000000000000 : ℝ)^55 := by
    have hnat : (2456119681 : ℕ)^71*20000000000000^55 ≤ 3265108101323^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2456119681 10000000000 3265108101323 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (911664677/1250000000 : ℝ)^71 ≤ (66534789155501/100000000000000 : ℝ)^55 := by
    have hnat : (911664677 : ℕ)^71*100000000000000^55 ≤ 66534789155501^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911664677 1250000000 66534789155501 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1275239133/5000000000 : ℝ), (-2456119681/10000000000 : ℝ), (-911664677/1250000000 : ℝ)] ![(685586812683/4000000000000 : ℝ), (3265108101323/20000000000000 : ℝ), (66534789155501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1275239133/5000000000 : ℝ)|^71 ≤ (685586812683/4000000000000 : ℝ)^55
        have hw : |(1275239133/5000000000 : ℝ)|=(1275239133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2456119681/10000000000 : ℝ)|^71 ≤ (3265108101323/20000000000000 : ℝ)^55
        have hw : |(-2456119681/10000000000 : ℝ)|=(2456119681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-911664677/1250000000 : ℝ)|^71 ≤ (66534789155501/100000000000000 : ℝ)^55
        have hw : |(-911664677/1250000000 : ℝ)|=(911664677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s0_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-29616339/2000000000 : ℝ)*x 0 + (-808934901/1250000000 : ℝ)*x 1 + (-1289539169/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29616339/2000000000 : ℝ)^71 ≤ (86958810663/20000000000000 : ℝ)^55 := by
    have hnat : (29616339 : ℕ)^71*20000000000000^55 ≤ 86958810663^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29616339 2000000000 86958810663 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (808934901/1250000000 : ℝ)^71 ≤ (14254854419839/25000000000000 : ℝ)^55 := by
    have hnat : (808934901 : ℕ)^71*25000000000000^55 ≤ 14254854419839^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808934901 1250000000 14254854419839 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1289539169/2500000000 : ℝ)^71 ≤ (21272894129361/50000000000000 : ℝ)^55 := by
    have hnat : (1289539169 : ℕ)^71*50000000000000^55 ≤ 21272894129361^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289539169 2500000000 21272894129361 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-29616339/2000000000 : ℝ), (-808934901/1250000000 : ℝ), (-1289539169/2500000000 : ℝ)] ![(86958810663/20000000000000 : ℝ), (14254854419839/25000000000000 : ℝ), (21272894129361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-29616339/2000000000 : ℝ)|^71 ≤ (86958810663/20000000000000 : ℝ)^55
        have hw : |(-29616339/2000000000 : ℝ)|=(29616339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-808934901/1250000000 : ℝ)|^71 ≤ (14254854419839/25000000000000 : ℝ)^55
        have hw : |(-808934901/1250000000 : ℝ)|=(808934901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1289539169/2500000000 : ℝ)|^71 ≤ (21272894129361/50000000000000 : ℝ)^55
        have hw : |(-1289539169/2500000000 : ℝ)|=(1289539169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s0_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4538537451/5000000000 : ℝ)*x 0 + (850978869/5000000000 : ℝ)*x 1 + (-402892983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4538537451/5000000000 : ℝ)^71 ≤ (88249449458569/100000000000000 : ℝ)^55 := by
    have hnat : (4538537451 : ℕ)^71*100000000000000^55 ≤ 88249449458569^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538537451 5000000000 88249449458569 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (850978869/5000000000 : ℝ)^71 ≤ (10167748094789/100000000000000 : ℝ)^55 := by
    have hnat : (850978869 : ℕ)^71*100000000000000^55 ≤ 10167748094789^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850978869 5000000000 10167748094789 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (402892983/10000000000 : ℝ)^71 ≤ (791401214767/50000000000000 : ℝ)^55 := by
    have hnat : (402892983 : ℕ)^71*50000000000000^55 ≤ 791401214767^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402892983 10000000000 791401214767 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4538537451/5000000000 : ℝ), (850978869/5000000000 : ℝ), (-402892983/10000000000 : ℝ)] ![(88249449458569/100000000000000 : ℝ), (10167748094789/100000000000000 : ℝ), (791401214767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4538537451/5000000000 : ℝ)|^71 ≤ (88249449458569/100000000000000 : ℝ)^55
        have hw : |(4538537451/5000000000 : ℝ)|=(4538537451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(850978869/5000000000 : ℝ)|^71 ≤ (10167748094789/100000000000000 : ℝ)^55
        have hw : |(850978869/5000000000 : ℝ)|=(850978869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-402892983/10000000000 : ℝ)|^71 ≤ (791401214767/50000000000000 : ℝ)^55
        have hw : |(-402892983/10000000000 : ℝ)|=(402892983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s0_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3489062981/10000000000 : ℝ)*x 0 + (-4710981493/10000000000 : ℝ)*x 1 + (4577712571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3489062981/10000000000 : ℝ)^71 ≤ (25684945248401/100000000000000 : ℝ)^55 := by
    have hnat : (3489062981 : ℕ)^71*100000000000000^55 ≤ 25684945248401^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3489062981 10000000000 25684945248401 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4710981493/10000000000 : ℝ)^71 ≤ (18922849551103/50000000000000 : ℝ)^55 := by
    have hnat : (4710981493 : ℕ)^71*50000000000000^55 ≤ 18922849551103^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4710981493 10000000000 18922849551103 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4577712571/10000000000 : ℝ)^71 ≤ (2279334726977/6250000000000 : ℝ)^55 := by
    have hnat : (4577712571 : ℕ)^71*6250000000000^55 ≤ 2279334726977^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4577712571 10000000000 2279334726977 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3489062981/10000000000 : ℝ), (-4710981493/10000000000 : ℝ), (4577712571/10000000000 : ℝ)] ![(25684945248401/100000000000000 : ℝ), (18922849551103/50000000000000 : ℝ), (2279334726977/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3489062981/10000000000 : ℝ)|^71 ≤ (25684945248401/100000000000000 : ℝ)^55
        have hw : |(3489062981/10000000000 : ℝ)|=(3489062981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4710981493/10000000000 : ℝ)|^71 ≤ (18922849551103/50000000000000 : ℝ)^55
        have hw : |(-4710981493/10000000000 : ℝ)|=(4710981493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4577712571/10000000000 : ℝ)|^71 ≤ (2279334726977/6250000000000 : ℝ)^55
        have hw : |(4577712571/10000000000 : ℝ)|=(4577712571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s0_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (10943023/25000000 : ℝ)*x 0 + (-3206677007/10000000000 : ℝ)*x 1 + (-1289539169/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10943023/25000000 : ℝ)^71 ≤ (34420592123751/100000000000000 : ℝ)^55 := by
    have hnat : (10943023 : ℕ)^71*100000000000000^55 ≤ 34420592123751^55*25000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10943023 25000000 34420592123751 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3206677007/10000000000 : ℝ)^71 ≤ (2879202450033/12500000000000 : ℝ)^55 := by
    have hnat : (3206677007 : ℕ)^71*12500000000000^55 ≤ 2879202450033^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3206677007 10000000000 2879202450033 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1289539169/2500000000 : ℝ)^71 ≤ (21272894129361/50000000000000 : ℝ)^55 := by
    have hnat : (1289539169 : ℕ)^71*50000000000000^55 ≤ 21272894129361^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289539169 2500000000 21272894129361 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10943023/25000000 : ℝ), (-3206677007/10000000000 : ℝ), (-1289539169/2500000000 : ℝ)] ![(34420592123751/100000000000000 : ℝ), (2879202450033/12500000000000 : ℝ), (21272894129361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10943023/25000000 : ℝ)|^71 ≤ (34420592123751/100000000000000 : ℝ)^55
        have hw : |(10943023/25000000 : ℝ)|=(10943023/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3206677007/10000000000 : ℝ)|^71 ≤ (2879202450033/12500000000000 : ℝ)^55
        have hw : |(-3206677007/10000000000 : ℝ)|=(3206677007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1289539169/2500000000 : ℝ)|^71 ≤ (21272894129361/50000000000000 : ℝ)^55
        have hw : |(-1289539169/2500000000 : ℝ)|=(1289539169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1147892621/5000000000 : ℝ)*x 0 + (-1212586589/2500000000 : ℝ)*x 1 + (-1091132561/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1147892621/5000000000 : ℝ)^71 ≤ (14963057799419/100000000000000 : ℝ)^55 := by
    have hnat : (1147892621 : ℕ)^71*100000000000000^55 ≤ 14963057799419^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147892621 5000000000 14963057799419 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1212586589/2500000000 : ℝ)^71 ≤ (39297162160279/100000000000000 : ℝ)^55 := by
    have hnat : (1212586589 : ℕ)^71*100000000000000^55 ≤ 39297162160279^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212586589 2500000000 39297162160279 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091132561/2000000000 : ℝ)^71 ≤ (2286989001307/5000000000000 : ℝ)^55 := by
    have hnat : (1091132561 : ℕ)^71*5000000000000^55 ≤ 2286989001307^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091132561 2000000000 2286989001307 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1147892621/5000000000 : ℝ), (-1212586589/2500000000 : ℝ), (-1091132561/2000000000 : ℝ)] ![(14963057799419/100000000000000 : ℝ), (39297162160279/100000000000000 : ℝ), (2286989001307/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1147892621/5000000000 : ℝ)|^71 ≤ (14963057799419/100000000000000 : ℝ)^55
        have hw : |(-1147892621/5000000000 : ℝ)|=(1147892621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1212586589/2500000000 : ℝ)|^71 ≤ (39297162160279/100000000000000 : ℝ)^55
        have hw : |(-1212586589/2500000000 : ℝ)|=(1212586589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1091132561/2000000000 : ℝ)|^71 ≤ (2286989001307/5000000000000 : ℝ)^55
        have hw : |(-1091132561/2000000000 : ℝ)|=(1091132561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3136191699/5000000000 : ℝ)*x 0 + (3338514083/10000000000 : ℝ)*x 1 + (-2981966251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3136191699/5000000000 : ℝ)^71 ≤ (27382550785581/50000000000000 : ℝ)^55 := by
    have hnat : (3136191699 : ℕ)^71*50000000000000^55 ≤ 27382550785581^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3136191699 5000000000 27382550785581 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3338514083/10000000000 : ℝ)^71 ≤ (12131667955009/50000000000000 : ℝ)^55 := by
    have hnat : (3338514083 : ℕ)^71*50000000000000^55 ≤ 12131667955009^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3338514083 10000000000 12131667955009 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2981966251/10000000000 : ℝ)^71 ≤ (5242890625093/25000000000000 : ℝ)^55 := by
    have hnat : (2981966251 : ℕ)^71*25000000000000^55 ≤ 5242890625093^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2981966251 10000000000 5242890625093 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3136191699/5000000000 : ℝ), (3338514083/10000000000 : ℝ), (-2981966251/10000000000 : ℝ)] ![(27382550785581/50000000000000 : ℝ), (12131667955009/50000000000000 : ℝ), (5242890625093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3136191699/5000000000 : ℝ)|^71 ≤ (27382550785581/50000000000000 : ℝ)^55
        have hw : |(3136191699/5000000000 : ℝ)|=(3136191699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3338514083/10000000000 : ℝ)|^71 ≤ (12131667955009/50000000000000 : ℝ)^55
        have hw : |(3338514083/10000000000 : ℝ)|=(3338514083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2981966251/10000000000 : ℝ)|^71 ≤ (5242890625093/25000000000000 : ℝ)^55
        have hw : |(-2981966251/10000000000 : ℝ)|=(2981966251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (530118017/1250000000 : ℝ)*x 0 + (-4523658437/10000000000 : ℝ)*x 1 + (1010134783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530118017/1250000000 : ℝ)^71 ≤ (6608730120017/20000000000000 : ℝ)^55 := by
    have hnat : (530118017 : ℕ)^71*20000000000000^55 ≤ 6608730120017^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530118017 1250000000 6608730120017 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523658437/10000000000 : ℝ)^71 ≤ (35914403548717/100000000000000 : ℝ)^55 := by
    have hnat : (4523658437 : ℕ)^71*100000000000000^55 ≤ 35914403548717^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523658437 10000000000 35914403548717 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010134783/2500000000 : ℝ)^71 ≤ (310419458327/1000000000000 : ℝ)^55 := by
    have hnat : (1010134783 : ℕ)^71*1000000000000^55 ≤ 310419458327^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010134783 2500000000 310419458327 1000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530118017/1250000000 : ℝ), (-4523658437/10000000000 : ℝ), (1010134783/2500000000 : ℝ)] ![(6608730120017/20000000000000 : ℝ), (35914403548717/100000000000000 : ℝ), (310419458327/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530118017/1250000000 : ℝ)|^71 ≤ (6608730120017/20000000000000 : ℝ)^55
        have hw : |(530118017/1250000000 : ℝ)|=(530118017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4523658437/10000000000 : ℝ)|^71 ≤ (35914403548717/100000000000000 : ℝ)^55
        have hw : |(-4523658437/10000000000 : ℝ)|=(4523658437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010134783/2500000000 : ℝ)|^71 ≤ (310419458327/1000000000000 : ℝ)^55
        have hw : |(1010134783/2500000000 : ℝ)|=(1010134783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310068_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1975217859/5000000000 : ℝ)*x 0 + (-2082331447/5000000000 : ℝ)*x 1 + (-936881401/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1975217859/5000000000 : ℝ)^71 ≤ (15075626424847/50000000000000 : ℝ)^55 := by
    have hnat : (1975217859 : ℕ)^71*50000000000000^55 ≤ 15075626424847^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975217859 5000000000 15075626424847 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082331447/5000000000 : ℝ)^71 ≤ (32278413031643/100000000000000 : ℝ)^55 := by
    have hnat : (2082331447 : ℕ)^71*100000000000000^55 ≤ 32278413031643^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082331447 5000000000 32278413031643 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (936881401/2000000000 : ℝ)^71 ≤ (3757033410417/10000000000000 : ℝ)^55 := by
    have hnat : (936881401 : ℕ)^71*10000000000000^55 ≤ 3757033410417^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936881401 2000000000 3757033410417 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1975217859/5000000000 : ℝ), (-2082331447/5000000000 : ℝ), (-936881401/2000000000 : ℝ)] ![(15075626424847/50000000000000 : ℝ), (32278413031643/100000000000000 : ℝ), (3757033410417/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1975217859/5000000000 : ℝ)|^71 ≤ (15075626424847/50000000000000 : ℝ)^55
        have hw : |(1975217859/5000000000 : ℝ)|=(1975217859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2082331447/5000000000 : ℝ)|^71 ≤ (32278413031643/100000000000000 : ℝ)^55
        have hw : |(-2082331447/5000000000 : ℝ)|=(2082331447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-936881401/2000000000 : ℝ)|^71 ≤ (3757033410417/10000000000000 : ℝ)^55
        have hw : |(-936881401/2000000000 : ℝ)|=(936881401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310068 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (35/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^35 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^35*1^8 ≤ 1^8*1^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11716741708364597/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (11716741708364597/10000000000000000 : ℝ)^35 := by
      have hnat : (2 : ℕ)^8*10000000000000000^35 ≤ 11716741708364597^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11716741708364597 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11716741708364597/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3213633126210889/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3213633126210889/2500000000000000 : ℝ)^35 := by
      have hnat : (3 : ℕ)^8*2500000000000000^35 ≤ 3213633126210889^35*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3213633126210889 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3213633126210889/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((7636715371/10000000000 : ℝ)*X 1 0+(714880383/2500000000 : ℝ)*X 1 1+(-809142993/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-243220073/5000000000 : ℝ)*X 0 0+(-1412115377/2500000000 : ℝ)*X 0 1+(-5858370687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((953912947/1250000000 : ℝ)*X 1 0+(1737061373/5000000000 : ℝ)*X 1 1+(-812620349/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((918591049/2000000000 : ℝ)*X 2 0+(-1469408237/5000000000 : ℝ)*X 2 1+(2590687001/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((128834799/250000000 : ℝ)*X 0 0+(-1325138831/10000000000 : ℝ)*X 0 1+(-5858370687/10000000000 : ℝ)*X 0 2+(128834799/250000000 : ℝ)*X 1 0+(-1325138831/10000000000 : ℝ)*X 1 1+(-5858370687/10000000000 : ℝ)*X 1 2+(128834799/250000000 : ℝ)*X 2 0+(-1325138831/10000000000 : ℝ)*X 2 1+(-5858370687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-166919767/10000000000 : ℝ)*X 0 0+(-1058099841/2500000000 : ℝ)*X 0 1+(-911664677/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((454246527/500000000 : ℝ)*X 1 0+(208994751/1250000000 : ℝ)*X 1 1+(-214357687/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4838191263/10000000000 : ℝ)*X 2 0+(-2224441699/5000000000 : ℝ)*X 2 1+(1744272529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1275239133/5000000000 : ℝ)*X 0 0+(-2456119681/10000000000 : ℝ)*X 0 1+(-911664677/1250000000 : ℝ)*X 0 2+(1275239133/5000000000 : ℝ)*X 1 0+(-2456119681/10000000000 : ℝ)*X 1 1+(-911664677/1250000000 : ℝ)*X 1 2+(1275239133/5000000000 : ℝ)*X 2 0+(-2456119681/10000000000 : ℝ)*X 2 1+(-911664677/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-29616339/2000000000 : ℝ)*X 0 0+(-808934901/1250000000 : ℝ)*X 0 1+(-1289539169/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4538537451/5000000000 : ℝ)*X 1 0+(850978869/5000000000 : ℝ)*X 1 1+(-402892983/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((3489062981/10000000000 : ℝ)*X 2 0+(-4710981493/10000000000 : ℝ)*X 2 1+(4577712571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((10943023/25000000 : ℝ)*X 0 0+(-3206677007/10000000000 : ℝ)*X 0 1+(-1289539169/2500000000 : ℝ)*X 0 2+(10943023/25000000 : ℝ)*X 1 0+(-3206677007/10000000000 : ℝ)*X 1 1+(-1289539169/2500000000 : ℝ)*X 1 2+(10943023/25000000 : ℝ)*X 2 0+(-3206677007/10000000000 : ℝ)*X 2 1+(-1289539169/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((23511/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23511/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13759920618093454533567/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (696422252061/500000000000 : ℝ)*(base1) + (1802817440357/1000000000000 : ℝ)*(base39) + (322111907693/1000000000000 : ℝ)*(base49) + (1198108788971/500000000000 : ℝ)*(major_s0_0) + (1198108788971/500000000000 : ℝ)*(major_s0_1) + (1198108788971/500000000000 : ℝ)*(major_s0_2) + (8014239/250000000000 : ℝ)*(sp_s0_1) + (2352115342421/500000000000 : ℝ)*(sp_s0_7) + (827839449119/250000000000 : ℝ)*(sp_s0_8) + (413921518269/125000000000 : ℝ)*(sp_s0_9) + (11024323471/125000000000 : ℝ)*(sp_s0_13) + (4024307/500000000000 : ℝ)*(sp_s0_14) + (4375901/1000000000000 : ℝ)*(sp_s0_15) + (22083181/1000000000000 : ℝ)*(sp_s0_23) + (148103909189/100000000000 : ℝ)*(f.failure) + (3311394229333/1000000000000 : ℝ)*(f.sum) + (446555761349249/2500000000000000000000000000 : ℝ)*base63 + (1597482847238811/5000000000000000000000000000 : ℝ)*base65 + (1821449646540313/5000000000000000000000000000 : ℝ)*base67 + (1126907264459687/5000000000000000000000000000 : ℝ)*base69 + (242095691849249/2500000000000000000000000000 : ℝ)*base71 + (245332037761189/5000000000000000000000000000 : ℝ)*base73 + (1149734086738811/5000000000000000000000000000 : ℝ)*base75 + (964379155040313/5000000000000000000000000000 : ℝ)*base76 + (498924876400751/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (4123/10000000000000000 : ℝ)*base86 + (4123/10000000000000000 : ℝ)*base88 + (4123/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-29563/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-29563/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2288861200863516468927/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (765851198089/500000000000 : ℝ)*(base1) + (606989571623/250000000000 : ℝ)*(base39) + (599657168569/1000000000000 : ℝ)*(base49) + (450607273159/1000000000000 : ℝ)*(base60) + (435556677217/125000000000 : ℝ)*(major_s0_0) + (435556677217/125000000000 : ℝ)*(major_s0_1) + (435556677217/125000000000 : ℝ)*(major_s0_2) + (684901/500000000000 : ℝ)*(sp_s0_8) + (8307981/200000000000 : ℝ)*(sp_s0_9) + (6346958954571/1000000000000 : ℝ)*(sp_s0_14) + (4813041308867/1000000000000 : ℝ)*(sp_s0_15) + (4815215018487/1000000000000 : ℝ)*(sp_s0_16) + (621946660169/1000000000000 : ℝ)*(sp_s0_20) + (553469931/250000000000 : ℝ)*(sp_s0_22) + (2153649056347/1000000000000 : ℝ)*(f.failure) + (601907069799/125000000000 : ℝ)*(f.sum) + (282351967242223/625000000000000000000000000 : ℝ)*base63 + (503837071447897/1250000000000000000000000000 : ℝ)*base65 + (308614500713451/1250000000000000000000000000 : ℝ)*base67 + (301523537463451/1250000000000000000000000000 : ℝ)*base68 + (128370126367223/625000000000000000000000000 : ℝ)*base71 + (421776935822897/1250000000000000000000000000 : ℝ)*base72 + (408737484822897/1250000000000000000000000000 : ℝ)*base75 + (190143035088451/1250000000000000000000000000 : ℝ)*base76 + (106184201554723/625000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (49829/100000000000000000 : ℝ)*base86 + (49829/100000000000000000 : ℝ)*base88 + (49829/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-21563/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-21563/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10592399721535654337499/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100320084451/500000000000 : ℝ)*(base1) + (3370977/500000000000 : ℝ)*(base10) + (1248084411271/1000000000000 : ℝ)*(base39) + (225563/125000000000 : ℝ)*(base43) + (249486193701/500000000000 : ℝ)*(base49) + (1539723336907/500000000000 : ℝ)*(major_s0_0) + (307944486931/100000000000 : ℝ)*(major_s0_1) + (1539723336907/500000000000 : ℝ)*(major_s0_2) + (4587091/500000000000 : ℝ)*(sp_s0_8) + (30583973/1000000000000 : ℝ)*(sp_s0_16) + (4456197110463/1000000000000 : ℝ)*(sp_s0_21) + (4255556313837/1000000000000 : ℝ)*(sp_s0_22) + (2127766549771/500000000000 : ℝ)*(sp_s0_23) + (851342433029/500000000000 : ℝ)*(sp_s0_27) + (23791562937/12500000000 : ℝ)*(f.failure) + (4255565488019/1000000000000 : ℝ)*(f.sum) + (632127872571333/2500000000000000000000000000 : ℝ)*base62 + (3632516838639813/5000000000000000000000000000 : ℝ)*base64 + (597113829981807/1000000000000000000000000000 : ℝ)*base66 + (2952712919281479/5000000000000000000000000000 : ℝ)*base69 + (281824553679167/2500000000000000000000000000 : ℝ)*base70 + (1098823057860187/5000000000000000000000000000 : ℝ)*base72 + (174927787915171/1000000000000000000000000000 : ℝ)*base75 + (1400530944718521/5000000000000000000000000000 : ℝ)*base76 + (709294545865389/2500000000000000000000000000 : ℝ)*base79 + (1459/1250000000000000 : ℝ)*base86 + (1459/1250000000000000 : ℝ)*base88 + (1459/1250000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (23511/100000 : ℝ) ^ (35/8 : ℝ) ≤ (2774157378345373/1562500000000000000 : ℝ) := by
    have hpowers : (23511/100000 : ℝ)^35 ≤ (2774157378345373/1562500000000000000 : ℝ)^8 := by
      have hnat : (23511 : ℕ)^35*1562500000000000000^8 ≤ 2774157378345373^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23511 100000 2774157378345373 1562500000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23511/100000 : ℝ)) (X := (2774157378345373/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (1565274157378345373/1562500000000000000 : ℝ) ≤ (2501013854927567/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (1565274157378345373/1562500000000000000 : ℝ)^8 ≤ (2501013854927567/2500000000000000 : ℝ)^35 := by
      have hnat : (1565274157378345373 : ℕ)^8*2500000000000000^35 ≤ 2501013854927567^35*1562500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1565274157378345373 1562500000000000000 2501013854927567 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501013854927567/2500000000000000 : ℝ)) (X := (1565274157378345373/1562500000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (784024157378345373/781250000000000000 : ℝ) ≤ (2502026324644943/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (784024157378345373/781250000000000000 : ℝ)^8 ≤ (2502026324644943/2500000000000000 : ℝ)^35 := by
      have hnat : (784024157378345373 : ℕ)^8*2500000000000000^35 ≤ 2502026324644943^35*781250000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        784024157378345373 781250000000000000 2502026324644943 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502026324644943/2500000000000000 : ℝ)) (X := (784024157378345373/781250000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(59638525151/34575000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2636639889/1530664062500 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (23511/100000 : ℝ)) (alpha := (59638525151/34575000000000 : ℝ)) (beta := (2636639889/1530664062500 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (23511/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(59638525151/34575000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2636639889/1530664062500 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (29563/50000 : ℝ) ^ (35/8 : ℝ) ≤ (10035313247321005473/100000000000000000000 : ℝ) := by
    have hpowers : (29563/50000 : ℝ)^35 ≤ (10035313247321005473/100000000000000000000 : ℝ)^8 := by
      have hnat : (29563 : ℕ)^35*100000000000000000000^8 ≤ 10035313247321005473^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29563 50000 10035313247321005473 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29563/50000 : ℝ)) (X := (10035313247321005473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (110035313247321005473/100000000000000000000 : ℝ) ≤ (638811999173031/625000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (110035313247321005473/100000000000000000000 : ℝ)^8 ≤ (638811999173031/625000000000000 : ℝ)^35 := by
      have hnat : (110035313247321005473 : ℕ)^8*625000000000000^35 ≤ 638811999173031^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110035313247321005473 100000000000000000000 638811999173031 625000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (638811999173031/625000000000000 : ℝ)) (X := (110035313247321005473/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (60035313247321005473/50000000000000000000 : ℝ) ≤ (2085388494809511/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (60035313247321005473/50000000000000000000 : ℝ)^8 ≤ (2085388494809511/2000000000000000 : ℝ)^35 := by
      have hnat : (60035313247321005473 : ℕ)^8*2000000000000000^35 ≤ 2085388494809511^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60035313247321005473 50000000000000000000 2085388494809511 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2085388494809511/2000000000000000 : ℝ)) (X := (60035313247321005473/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(13811999173031/369537500000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(12114734545827/347800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (29563/50000 : ℝ)) (alpha := (13811999173031/369537500000000 : ℝ)) (beta := (12114734545827/347800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (29563/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(13811999173031/369537500000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(12114734545827/347800000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (21563/50000 : ℝ) ^ (35/8 : ℝ) ≤ (2523387260750114627/100000000000000000000 : ℝ) := by
    have hpowers : (21563/50000 : ℝ)^35 ≤ (2523387260750114627/100000000000000000000 : ℝ)^8 := by
      have hnat : (21563 : ℕ)^35*100000000000000000000^8 ≤ 2523387260750114627^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21563 50000 2523387260750114627 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21563/50000 : ℝ)) (X := (2523387260750114627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (102523387260750114627/100000000000000000000 : ℝ) ≤ (628570266625523/625000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (102523387260750114627/100000000000000000000 : ℝ)^8 ≤ (628570266625523/625000000000000 : ℝ)^35 := by
      have hnat : (102523387260750114627 : ℕ)^8*625000000000000^35 ≤ 628570266625523^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102523387260750114627 100000000000000000000 628570266625523 625000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (628570266625523/625000000000000 : ℝ)) (X := (102523387260750114627/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (52523387260750114627/50000000000000000000 : ℝ) ≤ (2528293498949279/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (52523387260750114627/50000000000000000000 : ℝ)^8 ≤ (2528293498949279/2500000000000000 : ℝ)^35 := by
      have hnat : (52523387260750114627 : ℕ)^8*2500000000000000^35 ≤ 2528293498949279^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52523387260750114627 50000000000000000000 2528293498949279 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528293498949279/2500000000000000 : ℝ)) (X := (52523387260750114627/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(3570266625523/269537500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(14012432447187/1078150000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (21563/50000 : ℝ)) (alpha := (3570266625523/269537500000000 : ℝ)) (beta := (14012432447187/1078150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (21563/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(3570266625523/269537500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(14012432447187/1078150000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1147892621/5000000000 : ℝ)*X 0 0+(-1212586589/2500000000 : ℝ)*X 0 1+(-1091132561/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3136191699/5000000000 : ℝ)*X 1 0+(3338514083/10000000000 : ℝ)*X 1 1+(-2981966251/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((530118017/1250000000 : ℝ)*X 2 0+(-4523658437/10000000000 : ℝ)*X 2 1+(1010134783/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1975217859/5000000000 : ℝ)*X 0 0+(-2082331447/5000000000 : ℝ)*X 0 1+(-936881401/2000000000 : ℝ)*X 0 2+(1975217859/5000000000 : ℝ)*X 1 0+(-2082331447/5000000000 : ℝ)*X 1 1+(-936881401/2000000000 : ℝ)*X 1 2+(1975217859/5000000000 : ℝ)*X 2 0+(-2082331447/5000000000 : ℝ)*X 2 1+(-936881401/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310068_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-3910515270109018049552167105636311/587744545418000000000000000000000 : ℝ) := by norm_num
    linear_combination (3153/250000000000 : ℝ)*(base3) + (52259/1000000000000 : ℝ)*(base12) + (139/8000000000 : ℝ)*(base21) + (10607/250000000000 : ℝ)*(base25) + (680771181213/1000000000000 : ℝ)*(base39) + (48852992841/250000000000 : ℝ)*(base40) + (45193913329/200000000000 : ℝ)*(base49) + (146777415747/1000000000000 : ℝ)*(base60) + (161793/100000 : ℝ)*(major_s1_0) + (161793/100000 : ℝ)*(major_s1_1) + (161793/100000 : ℝ)*(major_s1_2) + (88712354337/40000000000 : ℝ)*(sp_s1_0) + (443561784659/200000000000 : ℝ)*(sp_s1_1) + (6930652659/3125000000 : ℝ)*(sp_s1_2) + (249999996847/250000000000 : ℝ)*(sp_s1_6) + (2217808910683/1000000000000 : ℝ)*(f.sum) + (63909677446703081/187490285000000000000000000000 : ℝ)*base63 + (26352812799709/53907500000000000000000000 : ℝ)*base65 + (40661786245319/59126000000000000000000000 : ℝ)*base67 + (39354587613189/107815000000000000000000000 : ℝ)*base69 + (3073826030121141/99405430000000000000000000000 : ℝ)*base71 + (12529908594489/15674000000000000000000000 : ℝ)*base73 + (744185980613/2173750000000000000000000 : ℝ)*base75 + (177366005731/576250000000000000000000 : ℝ)*base76 + (4700910523277577/6814271500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p010_b030 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 69)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=68 := by omega
  rcases hc with rfl
  · exact collision_c310068 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 68 ≤ c.val) (hhi : c.val < 69)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010_b030 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

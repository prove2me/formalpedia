-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p008_b036
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:27:04.354506+00:00
-- url     : https://prove2.me/submissions/45452b3b-fcf5-484a-aeeb-e1ce1090c215

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
theorem collision_support_c308077_s0_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2761331659/5000000000 : ℝ)*x 0 + (370757407/1000000000 : ℝ)*x 1 + (3590661031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2761331659/5000000000 : ℝ)^69 ≤ (46164339479459/100000000000000 : ℝ)^53 := by
    have hnat : (2761331659 : ℕ)^69*100000000000000^53 ≤ 46164339479459^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761331659 5000000000 46164339479459 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (370757407/1000000000 : ℝ)^69 ≤ (27479178736403/100000000000000 : ℝ)^53 := by
    have hnat : (370757407 : ℕ)^69*100000000000000^53 ≤ 27479178736403^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370757407 1000000000 27479178736403 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3590661031/10000000000 : ℝ)^69 ≤ (26356481764559/100000000000000 : ℝ)^53 := by
    have hnat : (3590661031 : ℕ)^69*100000000000000^53 ≤ 26356481764559^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3590661031 10000000000 26356481764559 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2761331659/5000000000 : ℝ), (370757407/1000000000 : ℝ), (3590661031/10000000000 : ℝ)] ![(46164339479459/100000000000000 : ℝ), (27479178736403/100000000000000 : ℝ), (26356481764559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2761331659/5000000000 : ℝ)|^69 ≤ (46164339479459/100000000000000 : ℝ)^53
        have hw : |(-2761331659/5000000000 : ℝ)|=(2761331659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(370757407/1000000000 : ℝ)|^69 ≤ (27479178736403/100000000000000 : ℝ)^53
        have hw : |(370757407/1000000000 : ℝ)|=(370757407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3590661031/10000000000 : ℝ)|^69 ≤ (26356481764559/100000000000000 : ℝ)^53
        have hw : |(3590661031/10000000000 : ℝ)|=(3590661031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s0_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4434622407/10000000000 : ℝ)*x 0 + (546143459/1000000000 : ℝ)*x 1 + (-72081281/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4434622407/10000000000 : ℝ)^69 ≤ (8673359377909/25000000000000 : ℝ)^53 := by
    have hnat : (4434622407 : ℕ)^69*25000000000000^53 ≤ 8673359377909^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4434622407 10000000000 8673359377909 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546143459/1000000000 : ℝ)^69 ≤ (5687391478283/12500000000000 : ℝ)^53 := by
    have hnat : (546143459 : ℕ)^69*12500000000000^53 ≤ 5687391478283^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546143459 1000000000 5687391478283 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (72081281/250000000 : ℝ)^69 ≤ (19807430651349/100000000000000 : ℝ)^53 := by
    have hnat : (72081281 : ℕ)^69*100000000000000^53 ≤ 19807430651349^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72081281 250000000 19807430651349 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4434622407/10000000000 : ℝ), (546143459/1000000000 : ℝ), (-72081281/250000000 : ℝ)] ![(8673359377909/25000000000000 : ℝ), (5687391478283/12500000000000 : ℝ), (19807430651349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4434622407/10000000000 : ℝ)|^69 ≤ (8673359377909/25000000000000 : ℝ)^53
        have hw : |(4434622407/10000000000 : ℝ)|=(4434622407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546143459/1000000000 : ℝ)|^69 ≤ (5687391478283/12500000000000 : ℝ)^53
        have hw : |(546143459/1000000000 : ℝ)|=(546143459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-72081281/250000000 : ℝ)|^69 ≤ (19807430651349/100000000000000 : ℝ)^53
        have hw : |(-72081281/250000000 : ℝ)|=(72081281/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s0_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (521138557/2500000000 : ℝ)*x 0 + (212023507/312500000 : ℝ)*x 1 + (3622945867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521138557/2500000000 : ℝ)^69 ≤ (6492355319051/50000000000000 : ℝ)^53 := by
    have hnat : (521138557 : ℕ)^69*50000000000000^53 ≤ 6492355319051^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521138557 2500000000 6492355319051 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212023507/312500000 : ℝ)^69 ≤ (30174934330061/50000000000000 : ℝ)^53 := by
    have hnat : (212023507 : ℕ)^69*50000000000000^53 ≤ 30174934330061^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212023507 312500000 30174934330061 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3622945867/10000000000 : ℝ)^69 ≤ (26665420685363/100000000000000 : ℝ)^53 := by
    have hnat : (3622945867 : ℕ)^69*100000000000000^53 ≤ 26665420685363^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3622945867 10000000000 26665420685363 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(521138557/2500000000 : ℝ), (212023507/312500000 : ℝ), (3622945867/10000000000 : ℝ)] ![(6492355319051/50000000000000 : ℝ), (30174934330061/50000000000000 : ℝ), (26665420685363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(521138557/2500000000 : ℝ)|^69 ≤ (6492355319051/50000000000000 : ℝ)^53
        have hw : |(521138557/2500000000 : ℝ)|=(521138557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(212023507/312500000 : ℝ)|^69 ≤ (30174934330061/50000000000000 : ℝ)^53
        have hw : |(212023507/312500000 : ℝ)|=(212023507/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3622945867/10000000000 : ℝ)|^69 ≤ (26665420685363/100000000000000 : ℝ)^53
        have hw : |(3622945867/10000000000 : ℝ)|=(3622945867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s0_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1409407729/2500000000 : ℝ)*x 0 + (3463989519/10000000000 : ℝ)*x 1 + (1851140967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1409407729/2500000000 : ℝ)^69 ≤ (23709697195601/50000000000000 : ℝ)^53 := by
    have hnat : (1409407729 : ℕ)^69*50000000000000^53 ≤ 23709697195601^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1409407729 2500000000 23709697195601 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3463989519/10000000000 : ℝ)^69 ≤ (12576240124377/50000000000000 : ℝ)^53 := by
    have hnat : (3463989519 : ℕ)^69*50000000000000^53 ≤ 12576240124377^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3463989519 10000000000 12576240124377 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1851140967/5000000000 : ℝ)^69 ≤ (13714062677111/50000000000000 : ℝ)^53 := by
    have hnat : (1851140967 : ℕ)^69*50000000000000^53 ≤ 13714062677111^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851140967 5000000000 13714062677111 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1409407729/2500000000 : ℝ), (3463989519/10000000000 : ℝ), (1851140967/5000000000 : ℝ)] ![(23709697195601/50000000000000 : ℝ), (12576240124377/50000000000000 : ℝ), (13714062677111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1409407729/2500000000 : ℝ)|^69 ≤ (23709697195601/50000000000000 : ℝ)^53
        have hw : |(-1409407729/2500000000 : ℝ)|=(1409407729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3463989519/10000000000 : ℝ)|^69 ≤ (12576240124377/50000000000000 : ℝ)^53
        have hw : |(3463989519/10000000000 : ℝ)|=(3463989519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1851140967/5000000000 : ℝ)|^69 ≤ (13714062677111/50000000000000 : ℝ)^53
        have hw : |(1851140967/5000000000 : ℝ)|=(1851140967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s0_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (937135477/2500000000 : ℝ)*x 0 + (-2067430729/10000000000 : ℝ)*x 1 + (3346036237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (937135477/2500000000 : ℝ)^69 ≤ (27875139433827/100000000000000 : ℝ)^53 := by
    have hnat : (937135477 : ℕ)^69*100000000000000^53 ≤ 27875139433827^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937135477 2500000000 27875139433827 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067430729/10000000000 : ℝ)^69 ≤ (12846020700147/100000000000000 : ℝ)^53 := by
    have hnat : (2067430729 : ℕ)^69*100000000000000^53 ≤ 12846020700147^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067430729 10000000000 12846020700147 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3346036237/5000000000 : ℝ)^69 ≤ (59278839852833/100000000000000 : ℝ)^53 := by
    have hnat : (3346036237 : ℕ)^69*100000000000000^53 ≤ 59278839852833^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3346036237 5000000000 59278839852833 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(937135477/2500000000 : ℝ), (-2067430729/10000000000 : ℝ), (3346036237/5000000000 : ℝ)] ![(27875139433827/100000000000000 : ℝ), (12846020700147/100000000000000 : ℝ), (59278839852833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(937135477/2500000000 : ℝ)|^69 ≤ (27875139433827/100000000000000 : ℝ)^53
        have hw : |(937135477/2500000000 : ℝ)|=(937135477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2067430729/10000000000 : ℝ)|^69 ≤ (12846020700147/100000000000000 : ℝ)^53
        have hw : |(-2067430729/10000000000 : ℝ)|=(2067430729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3346036237/5000000000 : ℝ)|^69 ≤ (59278839852833/100000000000000 : ℝ)^53
        have hw : |(3346036237/5000000000 : ℝ)|=(3346036237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s0_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (422600331/1000000000 : ℝ)*x 0 + (1435581797/2500000000 : ℝ)*x 1 + (-2775253637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422600331/1000000000 : ℝ)^69 ≤ (16291947214253/50000000000000 : ℝ)^53 := by
    have hnat : (422600331 : ℕ)^69*50000000000000^53 ≤ 16291947214253^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422600331 1000000000 16291947214253 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1435581797/2500000000 : ℝ)^69 ≤ (24284533643247/50000000000000 : ℝ)^53 := by
    have hnat : (1435581797 : ℕ)^69*50000000000000^53 ≤ 24284533643247^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435581797 2500000000 24284533643247 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2775253637/10000000000 : ℝ)^69 ≤ (4711759566389/25000000000000 : ℝ)^53 := by
    have hnat : (2775253637 : ℕ)^69*25000000000000^53 ≤ 4711759566389^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2775253637 10000000000 4711759566389 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(422600331/1000000000 : ℝ), (1435581797/2500000000 : ℝ), (-2775253637/10000000000 : ℝ)] ![(16291947214253/50000000000000 : ℝ), (24284533643247/50000000000000 : ℝ), (4711759566389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(422600331/1000000000 : ℝ)|^69 ≤ (16291947214253/50000000000000 : ℝ)^53
        have hw : |(422600331/1000000000 : ℝ)|=(422600331/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1435581797/2500000000 : ℝ)|^69 ≤ (24284533643247/50000000000000 : ℝ)^53
        have hw : |(1435581797/2500000000 : ℝ)|=(1435581797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2775253637/10000000000 : ℝ)|^69 ≤ (4711759566389/25000000000000 : ℝ)^53
        have hw : |(-2775253637/10000000000 : ℝ)|=(2775253637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s0_12 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (906137413/5000000000 : ℝ)*x 0 + (364077171/500000000 : ℝ)*x 1 + (3235357849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (906137413/5000000000 : ℝ)^69 ≤ (5410802751497/50000000000000 : ℝ)^53 := by
    have hnat : (906137413 : ℕ)^69*50000000000000^53 ≤ 5410802751497^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906137413 5000000000 5410802751497 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364077171/500000000 : ℝ)^69 ≤ (1033833371661/1562500000000 : ℝ)^53 := by
    have hnat : (364077171 : ℕ)^69*1562500000000^53 ≤ 1033833371661^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364077171 500000000 1033833371661 1562500000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3235357849/10000000000 : ℝ)^69 ≤ (1438316168551/6250000000000 : ℝ)^53 := by
    have hnat : (3235357849 : ℕ)^69*6250000000000^53 ≤ 1438316168551^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3235357849 10000000000 1438316168551 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(906137413/5000000000 : ℝ), (364077171/500000000 : ℝ), (3235357849/10000000000 : ℝ)] ![(5410802751497/50000000000000 : ℝ), (1033833371661/1562500000000 : ℝ), (1438316168551/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(906137413/5000000000 : ℝ)|^69 ≤ (5410802751497/50000000000000 : ℝ)^53
        have hw : |(906137413/5000000000 : ℝ)|=(906137413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(364077171/500000000 : ℝ)|^69 ≤ (1033833371661/1562500000000 : ℝ)^53
        have hw : |(364077171/500000000 : ℝ)|=(364077171/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3235357849/10000000000 : ℝ)|^69 ≤ (1438316168551/6250000000000 : ℝ)^53
        have hw : |(3235357849/10000000000 : ℝ)|=(3235357849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s0_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5592540039/10000000000 : ℝ)*x 0 + (930999593/2500000000 : ℝ)*x 1 + (873485897/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5592540039/10000000000 : ℝ)^69 ≤ (4692622551959/10000000000000 : ℝ)^53 := by
    have hnat : (5592540039 : ℕ)^69*10000000000000^53 ≤ 4692622551959^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5592540039 10000000000 4692622551959 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (930999593/2500000000 : ℝ)^69 ≤ (27637764449551/100000000000000 : ℝ)^53 := by
    have hnat : (930999593 : ℕ)^69*100000000000000^53 ≤ 27637764449551^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930999593 2500000000 27637764449551 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (873485897/2500000000 : ℝ)^69 ≤ (25436010009969/100000000000000 : ℝ)^53 := by
    have hnat : (873485897 : ℕ)^69*100000000000000^53 ≤ 25436010009969^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873485897 2500000000 25436010009969 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5592540039/10000000000 : ℝ), (930999593/2500000000 : ℝ), (873485897/2500000000 : ℝ)] ![(4692622551959/10000000000000 : ℝ), (27637764449551/100000000000000 : ℝ), (25436010009969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5592540039/10000000000 : ℝ)|^69 ≤ (4692622551959/10000000000000 : ℝ)^53
        have hw : |(-5592540039/10000000000 : ℝ)|=(5592540039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(930999593/2500000000 : ℝ)|^69 ≤ (27637764449551/100000000000000 : ℝ)^53
        have hw : |(930999593/2500000000 : ℝ)|=(930999593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(873485897/2500000000 : ℝ)|^69 ≤ (25436010009969/100000000000000 : ℝ)^53
        have hw : |(873485897/2500000000 : ℝ)|=(873485897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s0_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1859426167/5000000000 : ℝ)*x 0 + (-1153390221/5000000000 : ℝ)*x 1 + (6545730083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1859426167/5000000000 : ℝ)^69 ≤ (1379402692427/5000000000000 : ℝ)^53 := by
    have hnat : (1859426167 : ℕ)^69*5000000000000^53 ≤ 1379402692427^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859426167 5000000000 1379402692427 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1153390221/5000000000 : ℝ)^69 ≤ (3703789297969/25000000000000 : ℝ)^53 := by
    have hnat : (1153390221 : ℕ)^69*25000000000000^53 ≤ 3703789297969^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153390221 5000000000 3703789297969 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6545730083/10000000000 : ℝ)^69 ≤ (3599799309359/6250000000000 : ℝ)^53 := by
    have hnat : (6545730083 : ℕ)^69*6250000000000^53 ≤ 3599799309359^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6545730083 10000000000 3599799309359 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1859426167/5000000000 : ℝ), (-1153390221/5000000000 : ℝ), (6545730083/10000000000 : ℝ)] ![(1379402692427/5000000000000 : ℝ), (3703789297969/25000000000000 : ℝ), (3599799309359/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1859426167/5000000000 : ℝ)|^69 ≤ (1379402692427/5000000000000 : ℝ)^53
        have hw : |(1859426167/5000000000 : ℝ)|=(1859426167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1153390221/5000000000 : ℝ)|^69 ≤ (3703789297969/25000000000000 : ℝ)^53
        have hw : |(-1153390221/5000000000 : ℝ)|=(1153390221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6545730083/10000000000 : ℝ)|^69 ≤ (3599799309359/6250000000000 : ℝ)^53
        have hw : |(6545730083/10000000000 : ℝ)|=(6545730083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s0_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4349469707/10000000000 : ℝ)*x 0 + (2728995757/5000000000 : ℝ)*x 1 + (-745898093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349469707/10000000000 : ℝ)^69 ≤ (8457169143937/25000000000000 : ℝ)^53 := by
    have hnat : (4349469707 : ℕ)^69*25000000000000^53 ≤ 8457169143937^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349469707 10000000000 8457169143937 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728995757/5000000000 : ℝ)^69 ≤ (11365447944647/25000000000000 : ℝ)^53 := by
    have hnat : (2728995757 : ℕ)^69*25000000000000^53 ≤ 11365447944647^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728995757 5000000000 11365447944647 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (745898093/2500000000 : ℝ)^69 ≤ (517738290849/2500000000000 : ℝ)^53 := by
    have hnat : (745898093 : ℕ)^69*2500000000000^53 ≤ 517738290849^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745898093 2500000000 517738290849 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349469707/10000000000 : ℝ), (2728995757/5000000000 : ℝ), (-745898093/2500000000 : ℝ)] ![(8457169143937/25000000000000 : ℝ), (11365447944647/25000000000000 : ℝ), (517738290849/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349469707/10000000000 : ℝ)|^69 ≤ (8457169143937/25000000000000 : ℝ)^53
        have hw : |(4349469707/10000000000 : ℝ)|=(4349469707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728995757/5000000000 : ℝ)|^69 ≤ (11365447944647/25000000000000 : ℝ)^53
        have hw : |(2728995757/5000000000 : ℝ)|=(2728995757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-745898093/2500000000 : ℝ)|^69 ≤ (517738290849/2500000000000 : ℝ)^53
        have hw : |(-745898093/2500000000 : ℝ)|=(745898093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s0_17 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (2499999987/2500000000 : ℝ)*x 1 + (-5233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^69 ≤ (0 : ℝ)^53 := by
    have hnat : (0 : ℕ)^69*1^53 ≤ 0^53*1^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2499999987/2500000000 : ℝ)^69 ≤ (99999999323019/100000000000000 : ℝ)^53 := by
    have hnat : (2499999987 : ℕ)^69*100000000000000^53 ≤ 99999999323019^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2499999987 2500000000 99999999323019 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233/10000000000 : ℝ)^69 ≤ (332273/50000000000000 : ℝ)^53 := by
    have hnat : (5233 : ℕ)^69*50000000000000^53 ≤ 332273^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233 10000000000 332273 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (2499999987/2500000000 : ℝ), (-5233/10000000000 : ℝ)] ![(0 : ℝ), (99999999323019/100000000000000 : ℝ), (332273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^69 ≤ (0 : ℝ)^53
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2499999987/2500000000 : ℝ)|^69 ≤ (99999999323019/100000000000000 : ℝ)^53
        have hw : |(2499999987/2500000000 : ℝ)|=(2499999987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5233/10000000000 : ℝ)|^69 ≤ (332273/50000000000000 : ℝ)^53
        have hw : |(-5233/10000000000 : ℝ)|=(5233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s0_19 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (136682183/625000000 : ℝ)*x 0 + (3387310613/5000000000 : ℝ)*x 1 + (3547685143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136682183/625000000 : ℝ)^69 ≤ (2764177014631/20000000000000 : ℝ)^53 := by
    have hnat : (136682183 : ℕ)^69*20000000000000^53 ≤ 2764177014631^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136682183 625000000 2764177014631 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3387310613/5000000000 : ℝ)^69 ≤ (60232576264169/100000000000000 : ℝ)^53 := by
    have hnat : (3387310613 : ℕ)^69*100000000000000^53 ≤ 60232576264169^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3387310613 5000000000 60232576264169 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3547685143/10000000000 : ℝ)^69 ≤ (25946538648263/100000000000000 : ℝ)^53 := by
    have hnat : (3547685143 : ℕ)^69*100000000000000^53 ≤ 25946538648263^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3547685143 10000000000 25946538648263 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136682183/625000000 : ℝ), (3387310613/5000000000 : ℝ), (3547685143/10000000000 : ℝ)] ![(2764177014631/20000000000000 : ℝ), (60232576264169/100000000000000 : ℝ), (25946538648263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136682183/625000000 : ℝ)|^69 ≤ (2764177014631/20000000000000 : ℝ)^53
        have hw : |(136682183/625000000 : ℝ)|=(136682183/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3387310613/5000000000 : ℝ)|^69 ≤ (60232576264169/100000000000000 : ℝ)^53
        have hw : |(3387310613/5000000000 : ℝ)|=(3387310613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3547685143/10000000000 : ℝ)|^69 ≤ (25946538648263/100000000000000 : ℝ)^53
        have hw : |(3547685143/10000000000 : ℝ)|=(3547685143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s0_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-693405573/1250000000 : ℝ)*x 0 + (474707171/1250000000 : ℝ)*x 1 + (1735374711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (693405573/1250000000 : ℝ)^69 ≤ (23216013124123/50000000000000 : ℝ)^53 := by
    have hnat : (693405573 : ℕ)^69*50000000000000^53 ≤ 23216013124123^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693405573 1250000000 23216013124123 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474707171/1250000000 : ℝ)^69 ≤ (28351572165409/100000000000000 : ℝ)^53 := by
    have hnat : (474707171 : ℕ)^69*100000000000000^53 ≤ 28351572165409^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474707171 1250000000 28351572165409 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1735374711/5000000000 : ℝ)^69 ≤ (12608200787913/50000000000000 : ℝ)^53 := by
    have hnat : (1735374711 : ℕ)^69*50000000000000^53 ≤ 12608200787913^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735374711 5000000000 12608200787913 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-693405573/1250000000 : ℝ), (474707171/1250000000 : ℝ), (1735374711/5000000000 : ℝ)] ![(23216013124123/50000000000000 : ℝ), (28351572165409/100000000000000 : ℝ), (12608200787913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-693405573/1250000000 : ℝ)|^69 ≤ (23216013124123/50000000000000 : ℝ)^53
        have hw : |(-693405573/1250000000 : ℝ)|=(693405573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(474707171/1250000000 : ℝ)|^69 ≤ (28351572165409/100000000000000 : ℝ)^53
        have hw : |(474707171/1250000000 : ℝ)|=(474707171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1735374711/5000000000 : ℝ)|^69 ≤ (12608200787913/50000000000000 : ℝ)^53
        have hw : |(1735374711/5000000000 : ℝ)|=(1735374711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s0_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3640525237/10000000000 : ℝ)*x 0 + (-561092607/2500000000 : ℝ)*x 1 + (832079817/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3640525237/10000000000 : ℝ)^69 ≤ (5366798171543/20000000000000 : ℝ)^53 := by
    have hnat : (3640525237 : ℕ)^69*20000000000000^53 ≤ 5366798171543^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3640525237 10000000000 5366798171543 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561092607/2500000000 : ℝ)^69 ≤ (14295473644103/100000000000000 : ℝ)^53 := by
    have hnat : (561092607 : ℕ)^69*100000000000000^53 ≤ 14295473644103^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561092607 2500000000 14295473644103 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832079817/1250000000 : ℝ)^69 ≤ (58870535479139/100000000000000 : ℝ)^53 := by
    have hnat : (832079817 : ℕ)^69*100000000000000^53 ≤ 58870535479139^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832079817 1250000000 58870535479139 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3640525237/10000000000 : ℝ), (-561092607/2500000000 : ℝ), (832079817/1250000000 : ℝ)] ![(5366798171543/20000000000000 : ℝ), (14295473644103/100000000000000 : ℝ), (58870535479139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3640525237/10000000000 : ℝ)|^69 ≤ (5366798171543/20000000000000 : ℝ)^53
        have hw : |(3640525237/10000000000 : ℝ)|=(3640525237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-561092607/2500000000 : ℝ)|^69 ≤ (14295473644103/100000000000000 : ℝ)^53
        have hw : |(-561092607/2500000000 : ℝ)|=(561092607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(832079817/1250000000 : ℝ)|^69 ≤ (58870535479139/100000000000000 : ℝ)^53
        have hw : |(832079817/1250000000 : ℝ)|=(832079817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s0_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4689197071/10000000000 : ℝ)*x 0 + (2588090461/5000000000 : ℝ)*x 1 + (-2933894077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4689197071/10000000000 : ℝ)^69 ≤ (37308471927057/100000000000000 : ℝ)^53 := by
    have hnat : (4689197071 : ℕ)^69*100000000000000^53 ≤ 37308471927057^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4689197071 10000000000 37308471927057 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588090461/5000000000 : ℝ)^69 ≤ (42429965362931/100000000000000 : ℝ)^53 := by
    have hnat : (2588090461 : ℕ)^69*100000000000000^53 ≤ 42429965362931^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588090461 5000000000 42429965362931 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2933894077/10000000000 : ℝ)^69 ≤ (506539067253/2500000000000 : ℝ)^53 := by
    have hnat : (2933894077 : ℕ)^69*2500000000000^53 ≤ 506539067253^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2933894077 10000000000 506539067253 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4689197071/10000000000 : ℝ), (2588090461/5000000000 : ℝ), (-2933894077/10000000000 : ℝ)] ![(37308471927057/100000000000000 : ℝ), (42429965362931/100000000000000 : ℝ), (506539067253/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4689197071/10000000000 : ℝ)|^69 ≤ (37308471927057/100000000000000 : ℝ)^53
        have hw : |(4689197071/10000000000 : ℝ)|=(4689197071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588090461/5000000000 : ℝ)|^69 ≤ (42429965362931/100000000000000 : ℝ)^53
        have hw : |(2588090461/5000000000 : ℝ)|=(2588090461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2933894077/10000000000 : ℝ)|^69 ≤ (506539067253/2500000000000 : ℝ)^53
        have hw : |(-2933894077/10000000000 : ℝ)|=(2933894077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s0_25 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (43142509/250000000 : ℝ)*x 0 + (7400074883/10000000000 : ℝ)*x 1 + (631082757/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43142509/250000000 : ℝ)^69 ≤ (10153489374469/100000000000000 : ℝ)^53 := by
    have hnat : (43142509 : ℕ)^69*100000000000000^53 ≤ 10153489374469^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43142509 250000000 10153489374469 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7400074883/10000000000 : ℝ)^69 ≤ (67570981065167/100000000000000 : ℝ)^53 := by
    have hnat : (7400074883 : ℕ)^69*100000000000000^53 ≤ 67570981065167^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7400074883 10000000000 67570981065167 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (631082757/2000000000 : ℝ)^69 ≤ (11137764777381/50000000000000 : ℝ)^53 := by
    have hnat : (631082757 : ℕ)^69*50000000000000^53 ≤ 11137764777381^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631082757 2000000000 11137764777381 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43142509/250000000 : ℝ), (7400074883/10000000000 : ℝ), (631082757/2000000000 : ℝ)] ![(10153489374469/100000000000000 : ℝ), (67570981065167/100000000000000 : ℝ), (11137764777381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43142509/250000000 : ℝ)|^69 ≤ (10153489374469/100000000000000 : ℝ)^53
        have hw : |(43142509/250000000 : ℝ)|=(43142509/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7400074883/10000000000 : ℝ)|^69 ≤ (67570981065167/100000000000000 : ℝ)^53
        have hw : |(7400074883/10000000000 : ℝ)|=(7400074883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(631082757/2000000000 : ℝ)|^69 ≤ (11137764777381/50000000000000 : ℝ)^53
        have hw : |(631082757/2000000000 : ℝ)|=(631082757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2431323821/5000000000 : ℝ)*x 0 + (4010993989/10000000000 : ℝ)*x 1 + (2005503803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2431323821/5000000000 : ℝ)^69 ≤ (1955752253469/5000000000000 : ℝ)^53 := by
    have hnat : (2431323821 : ℕ)^69*5000000000000^53 ≤ 1955752253469^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431323821 5000000000 1955752253469 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4010993989/10000000000 : ℝ)^69 ≤ (30442410182429/100000000000000 : ℝ)^53 := by
    have hnat : (4010993989 : ℕ)^69*100000000000000^53 ≤ 30442410182429^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010993989 10000000000 30442410182429 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2005503803/5000000000 : ℝ)^69 ≤ (30442544731871/100000000000000 : ℝ)^53 := by
    have hnat : (2005503803 : ℕ)^69*100000000000000^53 ≤ 30442544731871^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005503803 5000000000 30442544731871 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2431323821/5000000000 : ℝ), (4010993989/10000000000 : ℝ), (2005503803/5000000000 : ℝ)] ![(1955752253469/5000000000000 : ℝ), (30442410182429/100000000000000 : ℝ), (30442544731871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2431323821/5000000000 : ℝ)|^69 ≤ (1955752253469/5000000000000 : ℝ)^53
        have hw : |(-2431323821/5000000000 : ℝ)|=(2431323821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4010993989/10000000000 : ℝ)|^69 ≤ (30442410182429/100000000000000 : ℝ)^53
        have hw : |(4010993989/10000000000 : ℝ)|=(4010993989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2005503803/5000000000 : ℝ)|^69 ≤ (30442544731871/100000000000000 : ℝ)^53
        have hw : |(2005503803/5000000000 : ℝ)|=(2005503803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4151332033/10000000000 : ℝ)*x 0 + (-428032449/1250000000 : ℝ)*x 1 + (329096417/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4151332033/10000000000 : ℝ)^69 ≤ (7959088237669/25000000000000 : ℝ)^53 := by
    have hnat : (4151332033 : ℕ)^69*25000000000000^53 ≤ 7959088237669^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151332033 10000000000 7959088237669 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428032449/1250000000 : ℝ)^69 ≤ (12388779221813/50000000000000 : ℝ)^53 := by
    have hnat : (428032449 : ℕ)^69*50000000000000^53 ≤ 12388779221813^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428032449 1250000000 12388779221813 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329096417/625000000 : ℝ)^69 ≤ (21693044292301/50000000000000 : ℝ)^53 := by
    have hnat : (329096417 : ℕ)^69*50000000000000^53 ≤ 21693044292301^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329096417 625000000 21693044292301 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4151332033/10000000000 : ℝ), (-428032449/1250000000 : ℝ), (329096417/625000000 : ℝ)] ![(7959088237669/25000000000000 : ℝ), (12388779221813/50000000000000 : ℝ), (21693044292301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4151332033/10000000000 : ℝ)|^69 ≤ (7959088237669/25000000000000 : ℝ)^53
        have hw : |(4151332033/10000000000 : ℝ)|=(4151332033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-428032449/1250000000 : ℝ)|^69 ≤ (12388779221813/50000000000000 : ℝ)^53
        have hw : |(-428032449/1250000000 : ℝ)|=(428032449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329096417/625000000 : ℝ)|^69 ≤ (21693044292301/50000000000000 : ℝ)^53
        have hw : |(329096417/625000000 : ℝ)|=(329096417/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4151321739/10000000000 : ℝ)*x 0 + (5265549501/10000000000 : ℝ)*x 1 + (-1712131363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4151321739/10000000000 : ℝ)^69 ≤ (31836250174357/100000000000000 : ℝ)^53 := by
    have hnat : (4151321739 : ℕ)^69*100000000000000^53 ≤ 31836250174357^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151321739 10000000000 31836250174357 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265549501/10000000000 : ℝ)^69 ≤ (5423270229961/12500000000000 : ℝ)^53 := by
    have hnat : (5265549501 : ℕ)^69*12500000000000^53 ≤ 5423270229961^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265549501 10000000000 5423270229961 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1712131363/5000000000 : ℝ)^69 ≤ (3097198495859/12500000000000 : ℝ)^53 := by
    have hnat : (1712131363 : ℕ)^69*12500000000000^53 ≤ 3097198495859^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1712131363 5000000000 3097198495859 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4151321739/10000000000 : ℝ), (5265549501/10000000000 : ℝ), (-1712131363/5000000000 : ℝ)] ![(31836250174357/100000000000000 : ℝ), (5423270229961/12500000000000 : ℝ), (3097198495859/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4151321739/10000000000 : ℝ)|^69 ≤ (31836250174357/100000000000000 : ℝ)^53
        have hw : |(4151321739/10000000000 : ℝ)|=(4151321739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265549501/10000000000 : ℝ)|^69 ≤ (5423270229961/12500000000000 : ℝ)^53
        have hw : |(5265549501/10000000000 : ℝ)|=(5265549501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1712131363/5000000000 : ℝ)|^69 ≤ (3097198495859/12500000000000 : ℝ)^53
        have hw : |(-1712131363/5000000000 : ℝ)|=(1712131363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308077_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3641306597/10000000000 : ℝ)*x 0 + (4618644697/10000000000 : ℝ)*x 1 + (2309313627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3641306597/10000000000 : ℝ)^69 ≤ (13420744551871/50000000000000 : ℝ)^53 := by
    have hnat : (3641306597 : ℕ)^69*50000000000000^53 ≤ 13420744551871^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3641306597 10000000000 13420744551871 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4618644697/10000000000 : ℝ)^69 ≤ (18289672683481/50000000000000 : ℝ)^53 := by
    have hnat : (4618644697 : ℕ)^69*50000000000000^53 ≤ 18289672683481^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4618644697 10000000000 18289672683481 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2309313627/5000000000 : ℝ)^69 ≤ (7315833102971/20000000000000 : ℝ)^53 := by
    have hnat : (2309313627 : ℕ)^69*20000000000000^53 ≤ 7315833102971^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2309313627 5000000000 7315833102971 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3641306597/10000000000 : ℝ), (4618644697/10000000000 : ℝ), (2309313627/5000000000 : ℝ)] ![(13420744551871/50000000000000 : ℝ), (18289672683481/50000000000000 : ℝ), (7315833102971/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3641306597/10000000000 : ℝ)|^69 ≤ (13420744551871/50000000000000 : ℝ)^53
        have hw : |(3641306597/10000000000 : ℝ)|=(3641306597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4618644697/10000000000 : ℝ)|^69 ≤ (18289672683481/50000000000000 : ℝ)^53
        have hw : |(4618644697/10000000000 : ℝ)|=(4618644697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2309313627/5000000000 : ℝ)|^69 ≤ (7315833102971/20000000000000 : ℝ)^53
        have hw : |(2309313627/5000000000 : ℝ)|=(2309313627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308077 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(147294478466963/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2761331659/5000000000 : ℝ)*X 0 0+(370757407/1000000000 : ℝ)*X 0 1+(3590661031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4434622407/10000000000 : ℝ)*X 2 0+(546143459/1000000000 : ℝ)*X 2 1+(-72081281/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((521138557/2500000000 : ℝ)*X 0 0+(212023507/312500000 : ℝ)*X 0 1+(3622945867/10000000000 : ℝ)*X 0 2+(521138557/2500000000 : ℝ)*X 1 0+(212023507/312500000 : ℝ)*X 1 1+(3622945867/10000000000 : ℝ)*X 1 2+(521138557/2500000000 : ℝ)*X 2 0+(212023507/312500000 : ℝ)*X 2 1+(3622945867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1409407729/2500000000 : ℝ)*X 0 0+(3463989519/10000000000 : ℝ)*X 0 1+(1851140967/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((937135477/2500000000 : ℝ)*X 1 0+(-2067430729/10000000000 : ℝ)*X 1 1+(3346036237/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((422600331/1000000000 : ℝ)*X 2 0+(1435581797/2500000000 : ℝ)*X 2 1+(-2775253637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((906137413/5000000000 : ℝ)*X 0 0+(364077171/500000000 : ℝ)*X 0 1+(3235357849/10000000000 : ℝ)*X 0 2+(906137413/5000000000 : ℝ)*X 1 0+(364077171/500000000 : ℝ)*X 1 1+(3235357849/10000000000 : ℝ)*X 1 2+(906137413/5000000000 : ℝ)*X 2 0+(364077171/500000000 : ℝ)*X 2 1+(3235357849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-5592540039/10000000000 : ℝ)*X 0 0+(930999593/2500000000 : ℝ)*X 0 1+(873485897/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((1859426167/5000000000 : ℝ)*X 1 0+(-1153390221/5000000000 : ℝ)*X 1 1+(6545730083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4349469707/10000000000 : ℝ)*X 2 0+(2728995757/5000000000 : ℝ)*X 2 1+(-745898093/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_17 : ((2499999987/2500000000 : ℝ)*X 0 1+(-5233/10000000000 : ℝ)*X 0 2+(2499999987/2500000000 : ℝ)*X 2 1+(-5233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_17 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((136682183/625000000 : ℝ)*X 0 0+(3387310613/5000000000 : ℝ)*X 0 1+(3547685143/10000000000 : ℝ)*X 0 2+(136682183/625000000 : ℝ)*X 1 0+(3387310613/5000000000 : ℝ)*X 1 1+(3547685143/10000000000 : ℝ)*X 1 2+(136682183/625000000 : ℝ)*X 2 0+(3387310613/5000000000 : ℝ)*X 2 1+(3547685143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-693405573/1250000000 : ℝ)*X 0 0+(474707171/1250000000 : ℝ)*X 0 1+(1735374711/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((3640525237/10000000000 : ℝ)*X 1 0+(-561092607/2500000000 : ℝ)*X 1 1+(832079817/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4689197071/10000000000 : ℝ)*X 2 0+(2588090461/5000000000 : ℝ)*X 2 1+(-2933894077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((43142509/250000000 : ℝ)*X 0 0+(7400074883/10000000000 : ℝ)*X 0 1+(631082757/2000000000 : ℝ)*X 0 2+(43142509/250000000 : ℝ)*X 1 0+(7400074883/10000000000 : ℝ)*X 1 1+(631082757/2000000000 : ℝ)*X 1 2+(43142509/250000000 : ℝ)*X 2 0+(7400074883/10000000000 : ℝ)*X 2 1+(631082757/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((21957/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21957/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17425534458284655357213/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (726867926631/500000000000 : ℝ)*(base49) + (2609108687473/1000000000000 : ℝ)*(base60) + (14380556403259/1000000000000 : ℝ)*(major_s0_0) + (5872050445191/250000000000 : ℝ)*(major_s0_1) + (14380556403259/1000000000000 : ℝ)*(major_s0_2) + (7745953/125000000000 : ℝ)*(sp_s0_0) + (56820707/1000000000000 : ℝ)*(sp_s0_6) + (979228393551/50000000000 : ℝ)*(sp_s0_7) + (2448042602633/125000000000 : ℝ)*(sp_s0_8) + (19584523852989/1000000000000 : ℝ)*(sp_s0_9) + (4588212492729/500000000000 : ℝ)*(sp_s0_12) + (13248207/125000000000 : ℝ)*(sp_s0_15) + (4553822688753/500000000000 : ℝ)*(sp_s0_17) + (289017581/1000000000000 : ℝ)*(sp_s0_21) + (1835296361233/200000000000 : ℝ)*(f.failure) + (3916925967729/200000000000 : ℝ)*(f.sum) + (7228556069625699/10000000000000000000000000000 : ℝ)*base62 + (878987397467583/1250000000000000000000000000 : ℝ)*base64 + (1398879115952193/2500000000000000000000000000 : ℝ)*base67 + (450146112572157/10000000000000000000000000000 : ℝ)*base69 + (1987977533312821/10000000000000000000000000000 : ℝ)*base70 + (147573341657417/1250000000000000000000000000 : ℝ)*base73 + (31871542837567/312500000000000000000000000 : ℝ)*base75 + (9741713957572157/10000000000000000000000000000 : ℝ)*base76 + (115006202267027/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (4663/20000000000000000 : ℝ)*base87 + (24663/20000000000000000 : ℝ)*base89 + (4663/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1271/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(1271/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (83052597168521167910313/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27331/7812500000 : ℝ)*(base40) + (1245634615901/1000000000000 : ℝ)*(base49) + (732952709299/500000000000 : ℝ)*(base60) + (8289506941027/1000000000000 : ℝ)*(major_s0_0) + (8289506941027/1000000000000 : ℝ)*(major_s0_1) + (8289506941027/1000000000000 : ℝ)*(major_s0_2) + (81821377/1000000000000 : ℝ)*(sp_s0_2) + (83048149/200000000000 : ℝ)*(sp_s0_7) + (70555720797/6250000000 : ℝ)*(sp_s0_13) + (5644659597161/500000000000 : ℝ)*(sp_s0_14) + (352784345209/31250000000 : ℝ)*(sp_s0_15) + (330604861059/62500000000 : ℝ)*(sp_s0_19) + (5686971/500000000000 : ℝ)*(sp_s0_21) + (748501/5000000000 : ℝ)*(sp_s0_22) + (330604861059/62500000000 : ℝ)*(f.failure) + (2257866113653/200000000000 : ℝ)*(f.sum) + (4984829964707213/10000000000000000000000000000 : ℝ)*base63 + (68733303916001/1250000000000000000000000000 : ℝ)*base65 + (2981452414964779/10000000000000000000000000000 : ℝ)*base66 + (3461191333035221/10000000000000000000000000000 : ℝ)*base69 + (5266619859292787/10000000000000000000000000000 : ℝ)*base71 + (28016469958999/1250000000000000000000000000 : ℝ)*base72 + (830079744666001/1250000000000000000000000000 : ℝ)*base74 + (2131866973035221/10000000000000000000000000000 : ℝ)*base76 + (1239055861363229/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1801/6250000000000000 : ℝ)*base86 + (1801/6250000000000000 : ℝ)*base88 + (1801/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(11217/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(11217/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20934317447638858857597/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92736913937/200000000000 : ℝ)*(base49) + (1451082774167/1000000000000 : ℝ)*(base60) + (2824677574131/250000000000 : ℝ)*(major_s0_0) + (5039457269729/250000000000 : ℝ)*(major_s0_1) + (2824677574131/250000000000 : ℝ)*(major_s0_2) + (297840537/500000000000 : ℝ)*(sp_s0_2) + (14970039/62500000000 : ℝ)*(sp_s0_8) + (1196546609/1000000000000 : ℝ)*(sp_s0_12) + (606652469/500000000000 : ℝ)*(sp_s0_14) + (1107389847799/125000000000 : ℝ)*(sp_s0_17) + (15387512517099/1000000000000 : ℝ)*(sp_s0_20) + (15386059691537/1000000000000 : ℝ)*(sp_s0_21) + (1923364604503/125000000000 : ℝ)*(sp_s0_22) + (144174118937/20000000000 : ℝ)*(sp_s0_25) + (7209902493459/1000000000000 : ℝ)*(f.failure) + (15387512517099/1000000000000 : ℝ)*(f.sum) + (205431393484403/2500000000000000000000000000 : ℝ)*base62 + (234758657378347/312500000000000000000000000 : ℝ)*base64 + (1437900656873033/2500000000000000000000000000 : ℝ)*base66 + (1465773584030187/2500000000000000000000000000 : ℝ)*base68 + (453993127746589/2500000000000000000000000000 : ℝ)*base70 + (232569669097097/312500000000000000000000000 : ℝ)*base72 + (132295939463027/312500000000000000000000000 : ℝ)*base74 + (543480646219813/2500000000000000000000000000 : ℝ)*base76 + (630942224899809/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (53349/100000000000000000 : ℝ)*base87 + (53349/100000000000000000 : ℝ)*base89 + (53349/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (21957/100000 : ℝ) ^ (17/4 : ℝ) ≤ (159105523912290943/100000000000000000000 : ℝ) := by
    have hpowers : (21957/100000 : ℝ)^17 ≤ (159105523912290943/100000000000000000000 : ℝ)^4 := by
      have hnat : (21957 : ℕ)^17*100000000000000000000^4 ≤ 159105523912290943^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21957 100000 159105523912290943 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21957/100000 : ℝ)) (X := (159105523912290943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100159105523912290943/100000000000000000000 : ℝ) ≤ (2500935346020039/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100159105523912290943/100000000000000000000 : ℝ)^4 ≤ (2500935346020039/2500000000000000 : ℝ)^17 := by
      have hnat : (100159105523912290943 : ℕ)^4*2500000000000000^17 ≤ 2500935346020039^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100159105523912290943 100000000000000000000 2500935346020039 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500935346020039/2500000000000000 : ℝ)) (X := (100159105523912290943/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50159105523912290943/50000000000000000000 : ℝ) ≤ (10007478226046173/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50159105523912290943/50000000000000000000 : ℝ)^4 ≤ (10007478226046173/10000000000000000 : ℝ)^17 := by
      have hnat : (50159105523912290943 : ℕ)^4*10000000000000000^17 ≤ 10007478226046173^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50159105523912290943 50000000000000000000 10007478226046173 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007478226046173/10000000000000000 : ℝ)) (X := (50159105523912290943/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(935346020039/548925000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3736841966017/2195700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (21957/100000 : ℝ)) (alpha := (935346020039/548925000000000 : ℝ)) (beta := (3736841966017/2195700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (21957/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(935346020039/548925000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3736841966017/2195700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1271/100000 : ℝ) ^ (17/4 : ℝ) ≤ (1711388577/195312500000000000 : ℝ) := by
    have hpowers : (1271/100000 : ℝ)^17 ≤ (1711388577/195312500000000000 : ℝ)^4 := by
      have hnat : (1271 : ℕ)^17*195312500000000000^4 ≤ 1711388577^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1271 100000 1711388577 195312500000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1271/100000 : ℝ)) (X := (1711388577/195312500000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (195312501711388577/195312500000000000 : ℝ) ≤ (10000000020617199/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (195312501711388577/195312500000000000 : ℝ)^4 ≤ (10000000020617199/10000000000000000 : ℝ)^17 := by
      have hnat : (195312501711388577 : ℕ)^4*10000000000000000^17 ≤ 10000000020617199^17*195312500000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195312501711388577 195312500000000000 10000000020617199 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000020617199/10000000000000000 : ℝ)) (X := (195312501711388577/195312500000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (97656251711388577/97656250000000000 : ℝ) ≤ (5000000020617199/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (97656251711388577/97656250000000000 : ℝ)^4 ≤ (5000000020617199/5000000000000000 : ℝ)^17 := by
      have hnat : (97656251711388577 : ℕ)^4*5000000000000000^17 ≤ 5000000020617199^17*97656250000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        97656251711388577 97656250000000000 5000000020617199 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000020617199/5000000000000000 : ℝ)) (X := (97656251711388577/97656250000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(20617199/127100000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(20617199/127100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1271/100000 : ℝ)) (alpha := (20617199/127100000000000 : ℝ)) (beta := (20617199/127100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1271/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(20617199/127100000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(20617199/127100000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (11217/100000 : ℝ) ^ (17/4 : ℝ) ≤ (9161699847484009/100000000000000000000 : ℝ) := by
    have hpowers : (11217/100000 : ℝ)^17 ≤ (9161699847484009/100000000000000000000 : ℝ)^4 := by
      have hnat : (11217 : ℕ)^17*100000000000000000000^4 ≤ 9161699847484009^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11217 100000 9161699847484009 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11217/100000 : ℝ)) (X := (9161699847484009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100009161699847484009/100000000000000000000 : ℝ) ≤ (10000215561857181/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100009161699847484009/100000000000000000000 : ℝ)^4 ≤ (10000215561857181/10000000000000000 : ℝ)^17 := by
      have hnat : (100009161699847484009 : ℕ)^4*10000000000000000^17 ≤ 10000215561857181^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100009161699847484009 100000000000000000000 10000215561857181 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000215561857181/10000000000000000 : ℝ)) (X := (100009161699847484009/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50009161699847484009/50000000000000000000 : ℝ) ≤ (5000215554306999/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50009161699847484009/50000000000000000000 : ℝ)^4 ≤ (5000215554306999/5000000000000000 : ℝ)^17 := by
      have hnat : (50009161699847484009 : ℕ)^4*5000000000000000^17 ≤ 5000215554306999^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009161699847484009 50000000000000000000 5000215554306999 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000215554306999/5000000000000000 : ℝ)) (X := (50009161699847484009/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(215561857181/1121700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(71848918939/373900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (11217/100000 : ℝ)) (alpha := (215561857181/1121700000000000 : ℝ)) (beta := (71848918939/373900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (11217/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(215561857181/1121700000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(71848918939/373900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2431323821/5000000000 : ℝ)*X 0 0+(4010993989/10000000000 : ℝ)*X 0 1+(2005503803/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4151332033/10000000000 : ℝ)*X 1 0+(-428032449/1250000000 : ℝ)*X 1 1+(329096417/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4151321739/10000000000 : ℝ)*X 2 0+(5265549501/10000000000 : ℝ)*X 2 1+(-1712131363/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3641306597/10000000000 : ℝ)*X 0 0+(4618644697/10000000000 : ℝ)*X 0 1+(2309313627/5000000000 : ℝ)*X 0 2+(3641306597/10000000000 : ℝ)*X 1 0+(4618644697/10000000000 : ℝ)*X 1 1+(2309313627/5000000000 : ℝ)*X 1 2+(3641306597/10000000000 : ℝ)*X 2 0+(4618644697/10000000000 : ℝ)*X 2 1+(2309313627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308077_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-320133/50000 : ℝ) < ((-156711/100000 : ℝ)*P 0+(-156711/100000 : ℝ)*P 1+(-156711/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-320133/50000 : ℝ) < (-4318485767245918367960156053611/684143525000000000000000000000 : ℝ) := by norm_num
    linear_combination (264519/1000000000000 : ℝ)*(base11) + (104477/1000000000000 : ℝ)*(base19) + (129043/500000000000 : ℝ)*(base23) + (18462621001/31250000000 : ℝ)*(base49) + (65324382289/250000000000 : ℝ)*(base50) + (25593/1000000000000 : ℝ)*(base53) + (13520683491/200000000000 : ℝ)*(base59) + (10287600619/31250000000 : ℝ)*(base60) + (156711/100000 : ℝ)*(major_s1_0) + (156711/100000 : ℝ)*(major_s1_1) + (1567109974407/1000000000000 : ℝ)*(major_s1_2) + (13150521461/6250000000 : ℝ)*(sp_s1_0) + (2104083593803/1000000000000 : ℝ)*(sp_s1_1) + (2104083465787/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (65752616371/31250000000 : ℝ)*(f.sum) + (184037277439766881/475226900000000000000000000000 : ℝ)*base63 + (98121697144573/373900000000000000000000000 : ℝ)*base65 + (14028223359/19859375000000000000000 : ℝ)*base66 + (93394013463501/373900000000000000000000000 : ℝ)*base69 + (281926842238781653/2736574100000000000000000000000 : ℝ)*base70 + (3466474672969/4574375000000000000000000 : ℝ)*base72 + (1089953793297/12710000000000000000000000 : ℝ)*base75 + (46381190718553/73190000000000000000000000 : ℝ)*base76 + (11874633857559231/46512245000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p008_b036 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (c : Fin 88) (hlo : 77 ≤ c.val) (hhi : c.val < 78)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=77 := by omega
  rcases hc with rfl
  · exact collision_c308077 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (c : Fin 88) (hlo : 77 ≤ c.val) (hhi : c.val < 78)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p008_b036 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

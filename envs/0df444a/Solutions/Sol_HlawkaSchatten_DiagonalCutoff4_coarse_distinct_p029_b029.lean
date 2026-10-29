-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b029
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:27:23.392874+00:00
-- url     : https://prove2.me/submissions/3781f46d-f57f-416e-9dc1-feaeb6354b73

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
theorem collision_support_c329059_s0_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-722998423/2500000000 : ℝ)*x 0 + (578398557/2000000000 : ℝ)*x 1 + (6083672123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (722998423/2500000000 : ℝ)^95 ≤ (4498862790133/20000000000000 : ℝ)^79 := by
    have hnat : (722998423 : ℕ)^95*20000000000000^79 ≤ 4498862790133^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722998423 2500000000 4498862790133 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (578398557/2000000000 : ℝ)^95 ≤ (4498861093417/20000000000000 : ℝ)^79 := by
    have hnat : (578398557 : ℕ)^95*20000000000000^79 ≤ 4498861093417^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578398557 2000000000 4498861093417 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6083672123/10000000000 : ℝ)^95 ≤ (13752845142361/25000000000000 : ℝ)^79 := by
    have hnat : (6083672123 : ℕ)^95*25000000000000^79 ≤ 13752845142361^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6083672123 10000000000 13752845142361 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-722998423/2500000000 : ℝ), (578398557/2000000000 : ℝ), (6083672123/10000000000 : ℝ)] ![(4498862790133/20000000000000 : ℝ), (4498861093417/20000000000000 : ℝ), (13752845142361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-722998423/2500000000 : ℝ)|^95 ≤ (4498862790133/20000000000000 : ℝ)^79
        have hw : |(-722998423/2500000000 : ℝ)|=(722998423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(578398557/2000000000 : ℝ)|^95 ≤ (4498861093417/20000000000000 : ℝ)^79
        have hw : |(578398557/2000000000 : ℝ)|=(578398557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6083672123/10000000000 : ℝ)|^95 ≤ (13752845142361/25000000000000 : ℝ)^79
        have hw : |(6083672123/10000000000 : ℝ)|=(6083672123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2891993227/10000000000 : ℝ)*x 0 + (-2891992067/10000000000 : ℝ)*x 1 + (6083673141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2891993227/10000000000 : ℝ)^95 ≤ (2249430960131/10000000000000 : ℝ)^79 := by
    have hnat : (2891993227 : ℕ)^95*10000000000000^79 ≤ 2249430960131^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2891993227 10000000000 2249430960131 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2891992067/10000000000 : ℝ)^95 ≤ (22494298751307/100000000000000 : ℝ)^79 := by
    have hnat : (2891992067 : ℕ)^95*100000000000000^79 ≤ 22494298751307^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2891992067 10000000000 22494298751307 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6083673141/10000000000 : ℝ)^95 ≤ (55011391639021/100000000000000 : ℝ)^79 := by
    have hnat : (6083673141 : ℕ)^95*100000000000000^79 ≤ 55011391639021^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6083673141 10000000000 55011391639021 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2891993227/10000000000 : ℝ), (-2891992067/10000000000 : ℝ), (6083673141/10000000000 : ℝ)] ![(2249430960131/10000000000000 : ℝ), (22494298751307/100000000000000 : ℝ), (55011391639021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2891993227/10000000000 : ℝ)|^95 ≤ (2249430960131/10000000000000 : ℝ)^79
        have hw : |(2891993227/10000000000 : ℝ)|=(2891993227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2891992067/10000000000 : ℝ)|^95 ≤ (22494298751307/100000000000000 : ℝ)^79
        have hw : |(-2891992067/10000000000 : ℝ)|=(2891992067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6083673141/10000000000 : ℝ)|^95 ≤ (55011391639021/100000000000000 : ℝ)^79
        have hw : |(6083673141/10000000000 : ℝ)|=(6083673141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s0_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1438189423/5000000000 : ℝ)*x 0 + (6286912969/10000000000 : ℝ)*x 1 + (2668746987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1438189423/5000000000 : ℝ)^95 ≤ (893933648359/4000000000000 : ℝ)^79 := by
    have hnat : (1438189423 : ℕ)^95*4000000000000^79 ≤ 893933648359^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1438189423 5000000000 893933648359 4000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6286912969/10000000000 : ℝ)^95 ≤ (11445760357963/20000000000000 : ℝ)^79 := by
    have hnat : (6286912969 : ℕ)^95*20000000000000^79 ≤ 11445760357963^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6286912969 10000000000 11445760357963 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2668746987/10000000000 : ℝ)^95 ≤ (5105714246411/25000000000000 : ℝ)^79 := by
    have hnat : (2668746987 : ℕ)^95*25000000000000^79 ≤ 5105714246411^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2668746987 10000000000 5105714246411 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1438189423/5000000000 : ℝ), (6286912969/10000000000 : ℝ), (2668746987/10000000000 : ℝ)] ![(893933648359/4000000000000 : ℝ), (11445760357963/20000000000000 : ℝ), (5105714246411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1438189423/5000000000 : ℝ)|^95 ≤ (893933648359/4000000000000 : ℝ)^79
        have hw : |(1438189423/5000000000 : ℝ)|=(1438189423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6286912969/10000000000 : ℝ)|^95 ≤ (11445760357963/20000000000000 : ℝ)^79
        have hw : |(6286912969/10000000000 : ℝ)|=(6286912969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2668746987/10000000000 : ℝ)|^95 ≤ (5105714246411/25000000000000 : ℝ)^79
        have hw : |(2668746987/10000000000 : ℝ)|=(2668746987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s0_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-580273621/2500000000 : ℝ)*x 0 + (163049303/2500000000 : ℝ)*x 1 + (1643655433/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (580273621/2500000000 : ℝ)^95 ≤ (17267344052479/100000000000000 : ℝ)^79 := by
    have hnat : (580273621 : ℕ)^95*100000000000000^79 ≤ 17267344052479^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580273621 2500000000 17267344052479 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163049303/2500000000 : ℝ)^95 ≤ (1875958201533/50000000000000 : ℝ)^79 := by
    have hnat : (163049303 : ℕ)^95*50000000000000^79 ≤ 1875958201533^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163049303 2500000000 1875958201533 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1643655433/2000000000 : ℝ)^95 ≤ (39490369763243/50000000000000 : ℝ)^79 := by
    have hnat : (1643655433 : ℕ)^95*50000000000000^79 ≤ 39490369763243^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1643655433 2000000000 39490369763243 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-580273621/2500000000 : ℝ), (163049303/2500000000 : ℝ), (1643655433/2000000000 : ℝ)] ![(17267344052479/100000000000000 : ℝ), (1875958201533/50000000000000 : ℝ), (39490369763243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-580273621/2500000000 : ℝ)|^95 ≤ (17267344052479/100000000000000 : ℝ)^79
        have hw : |(-580273621/2500000000 : ℝ)|=(580273621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163049303/2500000000 : ℝ)|^95 ≤ (1875958201533/50000000000000 : ℝ)^79
        have hw : |(163049303/2500000000 : ℝ)|=(163049303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1643655433/2000000000 : ℝ)|^95 ≤ (39490369763243/50000000000000 : ℝ)^79
        have hw : |(1643655433/2000000000 : ℝ)|=(1643655433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s0_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (466189943/2500000000 : ℝ)*x 0 + (-1192036989/10000000000 : ℝ)*x 1 + (513642291/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (466189943/2500000000 : ℝ)^95 ≤ (13270917388549/100000000000000 : ℝ)^79 := by
    have hnat : (466189943 : ℕ)^95*100000000000000^79 ≤ 13270917388549^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466189943 2500000000 13270917388549 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1192036989/10000000000 : ℝ)^95 ≤ (1549669790157/20000000000000 : ℝ)^79 := by
    have hnat : (1192036989 : ℕ)^95*20000000000000^79 ≤ 1549669790157^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192036989 10000000000 1549669790157 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513642291/625000000 : ℝ)^95 ≤ (19745183411021/25000000000000 : ℝ)^79 := by
    have hnat : (513642291 : ℕ)^95*25000000000000^79 ≤ 19745183411021^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513642291 625000000 19745183411021 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(466189943/2500000000 : ℝ), (-1192036989/10000000000 : ℝ), (513642291/625000000 : ℝ)] ![(13270917388549/100000000000000 : ℝ), (1549669790157/20000000000000 : ℝ), (19745183411021/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(466189943/2500000000 : ℝ)|^95 ≤ (13270917388549/100000000000000 : ℝ)^79
        have hw : |(466189943/2500000000 : ℝ)|=(466189943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1192036989/10000000000 : ℝ)|^95 ≤ (1549669790157/20000000000000 : ℝ)^79
        have hw : |(-1192036989/10000000000 : ℝ)|=(1192036989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513642291/625000000 : ℝ)|^95 ≤ (19745183411021/25000000000000 : ℝ)^79
        have hw : |(513642291/625000000 : ℝ)|=(513642291/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s0_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4131781993/10000000000 : ℝ)*x 0 + (7029214053/10000000000 : ℝ)*x 1 + (-1487759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4131781993/10000000000 : ℝ)^95 ≤ (34545626582417/100000000000000 : ℝ)^79 := by
    have hnat : (4131781993 : ℕ)^95*100000000000000^79 ≤ 34545626582417^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131781993 10000000000 34545626582417 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7029214053/10000000000 : ℝ)^95 ≤ (3272431382463/5000000000000 : ℝ)^79 := by
    have hnat : (7029214053 : ℕ)^95*5000000000000^79 ≤ 3272431382463^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7029214053 10000000000 3272431382463 5000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1487759/5000000000 : ℝ)^95 ≤ (2872879517/50000000000000 : ℝ)^79 := by
    have hnat : (1487759 : ℕ)^95*50000000000000^79 ≤ 2872879517^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1487759 5000000000 2872879517 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4131781993/10000000000 : ℝ), (7029214053/10000000000 : ℝ), (-1487759/5000000000 : ℝ)] ![(34545626582417/100000000000000 : ℝ), (3272431382463/5000000000000 : ℝ), (2872879517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4131781993/10000000000 : ℝ)|^95 ≤ (34545626582417/100000000000000 : ℝ)^79
        have hw : |(4131781993/10000000000 : ℝ)|=(4131781993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7029214053/10000000000 : ℝ)|^95 ≤ (3272431382463/5000000000000 : ℝ)^79
        have hw : |(7029214053/10000000000 : ℝ)|=(7029214053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1487759/5000000000 : ℝ)|^95 ≤ (2872879517/50000000000000 : ℝ)^79
        have hw : |(-1487759/5000000000 : ℝ)|=(1487759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s0_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2058060829/10000000000 : ℝ)*x 0 + (2000797579/2500000000 : ℝ)*x 1 + (647259927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2058060829/10000000000 : ℝ)^95 ≤ (2988420888367/20000000000000 : ℝ)^79 := by
    have hnat : (2058060829 : ℕ)^95*20000000000000^79 ≤ 2988420888367^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058060829 10000000000 2988420888367 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000797579/2500000000 : ℝ)^95 ≤ (76501661949449/100000000000000 : ℝ)^79 := by
    have hnat : (2000797579 : ℕ)^95*100000000000000^79 ≤ 76501661949449^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000797579 2500000000 76501661949449 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647259927/5000000000 : ℝ)^95 ≤ (855623359223/10000000000000 : ℝ)^79 := by
    have hnat : (647259927 : ℕ)^95*10000000000000^79 ≤ 855623359223^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647259927 5000000000 855623359223 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2058060829/10000000000 : ℝ), (2000797579/2500000000 : ℝ), (647259927/5000000000 : ℝ)] ![(2988420888367/20000000000000 : ℝ), (76501661949449/100000000000000 : ℝ), (855623359223/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2058060829/10000000000 : ℝ)|^95 ≤ (2988420888367/20000000000000 : ℝ)^79
        have hw : |(2058060829/10000000000 : ℝ)|=(2058060829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2000797579/2500000000 : ℝ)|^95 ≤ (76501661949449/100000000000000 : ℝ)^79
        have hw : |(2000797579/2500000000 : ℝ)|=(2000797579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647259927/5000000000 : ℝ)|^95 ≤ (855623359223/10000000000000 : ℝ)^79
        have hw : |(647259927/5000000000 : ℝ)|=(647259927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s0_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-986764233/10000000000 : ℝ)*x 0 + (519234509/2500000000 : ℝ)*x 1 + (1639137341/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (986764233/10000000000 : ℝ)^95 ≤ (6173191990229/100000000000000 : ℝ)^79 := by
    have hnat : (986764233 : ℕ)^95*100000000000000^79 ≤ 6173191990229^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986764233 10000000000 6173191990229 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519234509/2500000000 : ℝ)^95 ≤ (15107068768487/100000000000000 : ℝ)^79 := by
    have hnat : (519234509 : ℕ)^95*100000000000000^79 ≤ 15107068768487^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519234509 2500000000 15107068768487 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1639137341/2000000000 : ℝ)^95 ≤ (19679934806897/25000000000000 : ℝ)^79 := by
    have hnat : (1639137341 : ℕ)^95*25000000000000^79 ≤ 19679934806897^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1639137341 2000000000 19679934806897 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-986764233/10000000000 : ℝ), (519234509/2500000000 : ℝ), (1639137341/2000000000 : ℝ)] ![(6173191990229/100000000000000 : ℝ), (15107068768487/100000000000000 : ℝ), (19679934806897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-986764233/10000000000 : ℝ)|^95 ≤ (6173191990229/100000000000000 : ℝ)^79
        have hw : |(-986764233/10000000000 : ℝ)|=(986764233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(519234509/2500000000 : ℝ)|^95 ≤ (15107068768487/100000000000000 : ℝ)^79
        have hw : |(519234509/2500000000 : ℝ)|=(519234509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1639137341/2000000000 : ℝ)|^95 ≤ (19679934806897/25000000000000 : ℝ)^79
        have hw : |(1639137341/2000000000 : ℝ)|=(1639137341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s0_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (36327781/400000000 : ℝ)*x 0 + (-2143741787/10000000000 : ℝ)*x 1 + (8195686719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36327781/400000000 : ℝ)^95 ≤ (2793490108207/50000000000000 : ℝ)^79 := by
    have hnat : (36327781 : ℕ)^95*50000000000000^79 ≤ 2793490108207^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36327781 400000000 2793490108207 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2143741787/10000000000 : ℝ)^95 ≤ (15693280379203/100000000000000 : ℝ)^79 := by
    have hnat : (2143741787 : ℕ)^95*100000000000000^79 ≤ 15693280379203^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143741787 10000000000 15693280379203 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8195686719/10000000000 : ℝ)^95 ≤ (19679934847323/25000000000000 : ℝ)^79 := by
    have hnat : (8195686719 : ℕ)^95*25000000000000^79 ≤ 19679934847323^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8195686719 10000000000 19679934847323 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(36327781/400000000 : ℝ), (-2143741787/10000000000 : ℝ), (8195686719/10000000000 : ℝ)] ![(2793490108207/50000000000000 : ℝ), (15693280379203/100000000000000 : ℝ), (19679934847323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(36327781/400000000 : ℝ)|^95 ≤ (2793490108207/50000000000000 : ℝ)^79
        have hw : |(36327781/400000000 : ℝ)|=(36327781/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2143741787/10000000000 : ℝ)|^95 ≤ (15693280379203/100000000000000 : ℝ)^79
        have hw : |(-2143741787/10000000000 : ℝ)|=(2143741787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8195686719/10000000000 : ℝ)|^95 ≤ (19679934847323/25000000000000 : ℝ)^79
        have hw : |(8195686719/10000000000 : ℝ)|=(8195686719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s0_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (515185901/625000000 : ℝ)*x 0 + (1351171879/5000000000 : ℝ)*x 1 + (-880683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515185901/625000000 : ℝ)^95 ≤ (619267555199/781250000000 : ℝ)^79 := by
    have hnat : (515185901 : ℕ)^95*781250000000^79 ≤ 619267555199^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515185901 625000000 619267555199 781250000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351171879/5000000000 : ℝ)^95 ≤ (10366211974563/50000000000000 : ℝ)^79 := by
    have hnat : (1351171879 : ℕ)^95*50000000000000^79 ≤ 10366211974563^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351171879 5000000000 10366211974563 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880683/10000000000 : ℝ)^95 ≤ (664488181/50000000000000 : ℝ)^79 := by
    have hnat : (880683 : ℕ)^95*50000000000000^79 ≤ 664488181^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880683 10000000000 664488181 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(515185901/625000000 : ℝ), (1351171879/5000000000 : ℝ), (-880683/10000000000 : ℝ)] ![(619267555199/781250000000 : ℝ), (10366211974563/50000000000000 : ℝ), (664488181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(515185901/625000000 : ℝ)|^95 ≤ (619267555199/781250000000 : ℝ)^79
        have hw : |(515185901/625000000 : ℝ)|=(515185901/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351171879/5000000000 : ℝ)|^95 ≤ (10366211974563/50000000000000 : ℝ)^79
        have hw : |(1351171879/5000000000 : ℝ)|=(1351171879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-880683/10000000000 : ℝ)|^95 ≤ (664488181/50000000000000 : ℝ)^79
        have hw : |(-880683/10000000000 : ℝ)|=(880683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s0_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1653713067/2500000000 : ℝ)*x 0 + (351401527/1000000000 : ℝ)*x 1 + (156270023/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1653713067/2500000000 : ℝ)^95 ≤ (60837281557267/100000000000000 : ℝ)^79 := by
    have hnat : (1653713067 : ℕ)^95*100000000000000^79 ≤ 60837281557267^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1653713067 2500000000 60837281557267 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (351401527/1000000000 : ℝ)^95 ≤ (28432464728067/100000000000000 : ℝ)^79 := by
    have hnat : (351401527 : ℕ)^95*100000000000000^79 ≤ 28432464728067^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351401527 1000000000 28432464728067 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (156270023/1000000000 : ℝ)^95 ≤ (10730253697903/100000000000000 : ℝ)^79 := by
    have hnat : (156270023 : ℕ)^95*100000000000000^79 ≤ 10730253697903^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156270023 1000000000 10730253697903 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1653713067/2500000000 : ℝ), (351401527/1000000000 : ℝ), (156270023/1000000000 : ℝ)] ![(60837281557267/100000000000000 : ℝ), (28432464728067/100000000000000 : ℝ), (10730253697903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1653713067/2500000000 : ℝ)|^95 ≤ (60837281557267/100000000000000 : ℝ)^79
        have hw : |(1653713067/2500000000 : ℝ)|=(1653713067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(351401527/1000000000 : ℝ)|^95 ≤ (28432464728067/100000000000000 : ℝ)^79
        have hw : |(351401527/1000000000 : ℝ)|=(351401527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(156270023/1000000000 : ℝ)|^95 ≤ (10730253697903/100000000000000 : ℝ)^79
        have hw : |(156270023/1000000000 : ℝ)|=(156270023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s0_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4671359311/10000000000 : ℝ)*x 0 + (45425541/200000000 : ℝ)*x 1 + (2484969391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4671359311/10000000000 : ℝ)^95 ≤ (20020046421171/50000000000000 : ℝ)^79 := by
    have hnat : (4671359311 : ℕ)^95*50000000000000^79 ≤ 20020046421171^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4671359311 10000000000 20020046421171 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45425541/200000000 : ℝ)^95 ≤ (8411325577673/50000000000000 : ℝ)^79 := by
    have hnat : (45425541 : ℕ)^95*50000000000000^79 ≤ 8411325577673^79*200000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45425541 200000000 8411325577673 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2484969391/5000000000 : ℝ)^95 ≤ (10784313995181/25000000000000 : ℝ)^79 := by
    have hnat : (2484969391 : ℕ)^95*25000000000000^79 ≤ 10784313995181^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2484969391 5000000000 10784313995181 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4671359311/10000000000 : ℝ), (45425541/200000000 : ℝ), (2484969391/5000000000 : ℝ)] ![(20020046421171/50000000000000 : ℝ), (8411325577673/50000000000000 : ℝ), (10784313995181/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4671359311/10000000000 : ℝ)|^95 ≤ (20020046421171/50000000000000 : ℝ)^79
        have hw : |(-4671359311/10000000000 : ℝ)|=(4671359311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45425541/200000000 : ℝ)|^95 ≤ (8411325577673/50000000000000 : ℝ)^79
        have hw : |(45425541/200000000 : ℝ)|=(45425541/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2484969391/5000000000 : ℝ)|^95 ≤ (10784313995181/25000000000000 : ℝ)^79
        have hw : |(2484969391/5000000000 : ℝ)|=(2484969391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s0_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (950999147/5000000000 : ℝ)*x 0 + (-776021877/2500000000 : ℝ)*x 1 + (6712348821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (950999147/5000000000 : ℝ)^95 ≤ (13590247411661/100000000000000 : ℝ)^79 := by
    have hnat : (950999147 : ℕ)^95*100000000000000^79 ≤ 13590247411661^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950999147 5000000000 13590247411661 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776021877/2500000000 : ℝ)^95 ≤ (24492578243323/100000000000000 : ℝ)^79 := by
    have hnat : (776021877 : ℕ)^95*100000000000000^79 ≤ 24492578243323^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776021877 2500000000 24492578243323 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6712348821/10000000000 : ℝ)^95 ≤ (15479293582313/25000000000000 : ℝ)^79 := by
    have hnat : (6712348821 : ℕ)^95*25000000000000^79 ≤ 15479293582313^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6712348821 10000000000 15479293582313 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(950999147/5000000000 : ℝ), (-776021877/2500000000 : ℝ), (6712348821/10000000000 : ℝ)] ![(13590247411661/100000000000000 : ℝ), (24492578243323/100000000000000 : ℝ), (15479293582313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(950999147/5000000000 : ℝ)|^95 ≤ (13590247411661/100000000000000 : ℝ)^79
        have hw : |(950999147/5000000000 : ℝ)|=(950999147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-776021877/2500000000 : ℝ)|^95 ≤ (24492578243323/100000000000000 : ℝ)^79
        have hw : |(-776021877/2500000000 : ℝ)|=(776021877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6712348821/10000000000 : ℝ)|^95 ≤ (15479293582313/25000000000000 : ℝ)^79
        have hw : |(6712348821/10000000000 : ℝ)|=(6712348821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s0_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8316712237/10000000000 : ℝ)*x 0 + (2609542399/10000000000 : ℝ)*x 1 + (-357409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8316712237/10000000000 : ℝ)^95 ≤ (80119707646069/100000000000000 : ℝ)^79 := by
    have hnat : (8316712237 : ℕ)^95*100000000000000^79 ≤ 80119707646069^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8316712237 10000000000 80119707646069 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609542399/10000000000 : ℝ)^95 ≤ (9939629150927/50000000000000 : ℝ)^79 := by
    have hnat : (2609542399 : ℕ)^95*50000000000000^79 ≤ 9939629150927^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609542399 10000000000 9939629150927 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (357409/5000000000 : ℝ)^95 ≤ (517021821/50000000000000 : ℝ)^79 := by
    have hnat : (357409 : ℕ)^95*50000000000000^79 ≤ 517021821^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357409 5000000000 517021821 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8316712237/10000000000 : ℝ), (2609542399/10000000000 : ℝ), (-357409/5000000000 : ℝ)] ![(80119707646069/100000000000000 : ℝ), (9939629150927/50000000000000 : ℝ), (517021821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8316712237/10000000000 : ℝ)|^95 ≤ (80119707646069/100000000000000 : ℝ)^79
        have hw : |(8316712237/10000000000 : ℝ)|=(8316712237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609542399/10000000000 : ℝ)|^95 ≤ (9939629150927/50000000000000 : ℝ)^79
        have hw : |(2609542399/10000000000 : ℝ)|=(2609542399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-357409/5000000000 : ℝ)|^95 ≤ (517021821/50000000000000 : ℝ)^79
        have hw : |(-357409/5000000000 : ℝ)|=(357409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s0_27 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (404682631/5000000000 : ℝ)*x 0 + (8879946323/10000000000 : ℝ)*x 1 + (51231793/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404682631/5000000000 : ℝ)^95 ≤ (4864176011723/100000000000000 : ℝ)^79 := by
    have hnat : (404682631 : ℕ)^95*100000000000000^79 ≤ 4864176011723^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404682631 5000000000 4864176011723 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8879946323/10000000000 : ℝ)^95 ≤ (86688562616581/100000000000000 : ℝ)^79 := by
    have hnat : (8879946323 : ℕ)^95*100000000000000^79 ≤ 86688562616581^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8879946323 10000000000 86688562616581 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51231793/400000000 : ℝ)^95 ≤ (4223630680393/50000000000000 : ℝ)^79 := by
    have hnat : (51231793 : ℕ)^95*50000000000000^79 ≤ 4223630680393^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51231793 400000000 4223630680393 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(404682631/5000000000 : ℝ), (8879946323/10000000000 : ℝ), (51231793/400000000 : ℝ)] ![(4864176011723/100000000000000 : ℝ), (86688562616581/100000000000000 : ℝ), (4223630680393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(404682631/5000000000 : ℝ)|^95 ≤ (4864176011723/100000000000000 : ℝ)^79
        have hw : |(404682631/5000000000 : ℝ)|=(404682631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8879946323/10000000000 : ℝ)|^95 ≤ (86688562616581/100000000000000 : ℝ)^79
        have hw : |(8879946323/10000000000 : ℝ)|=(8879946323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51231793/400000000 : ℝ)|^95 ≤ (4223630680393/50000000000000 : ℝ)^79
        have hw : |(51231793/400000000 : ℝ)|=(51231793/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s1_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-320254717/1000000000 : ℝ)*x 0 + (1600848847/5000000000 : ℝ)*x 1 + (2769725327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (320254717/1000000000 : ℝ)^95 ≤ (25429787561939/100000000000000 : ℝ)^79 := by
    have hnat : (320254717 : ℕ)^95*100000000000000^79 ≤ 25429787561939^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320254717 1000000000 25429787561939 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1600848847/5000000000 : ℝ)^95 ≤ (12710838199199/50000000000000 : ℝ)^79 := by
    have hnat : (1600848847 : ℕ)^95*50000000000000^79 ≤ 12710838199199^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1600848847 5000000000 12710838199199 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2769725327/5000000000 : ℝ)^95 ≤ (49148536029739/100000000000000 : ℝ)^79 := by
    have hnat : (2769725327 : ℕ)^95*100000000000000^79 ≤ 49148536029739^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2769725327 5000000000 49148536029739 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-320254717/1000000000 : ℝ), (1600848847/5000000000 : ℝ), (2769725327/5000000000 : ℝ)] ![(25429787561939/100000000000000 : ℝ), (12710838199199/50000000000000 : ℝ), (49148536029739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-320254717/1000000000 : ℝ)|^95 ≤ (25429787561939/100000000000000 : ℝ)^79
        have hw : |(-320254717/1000000000 : ℝ)|=(320254717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1600848847/5000000000 : ℝ)|^95 ≤ (12710838199199/50000000000000 : ℝ)^79
        have hw : |(1600848847/5000000000 : ℝ)|=(1600848847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2769725327/5000000000 : ℝ)|^95 ≤ (49148536029739/100000000000000 : ℝ)^79
        have hw : |(2769725327/5000000000 : ℝ)|=(2769725327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s1_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1600842519/5000000000 : ℝ)*x 0 + (-40010401/125000000 : ℝ)*x 1 + (5540996789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1600842519/5000000000 : ℝ)^95 ≤ (12710777778371/50000000000000 : ℝ)^79 := by
    have hnat : (1600842519 : ℕ)^95*50000000000000^79 ≤ 12710777778371^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1600842519 5000000000 12710777778371 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40010401/125000000 : ℝ)^95 ≤ (5082682318123/20000000000000 : ℝ)^79 := by
    have hnat : (40010401 : ℕ)^95*20000000000000^79 ≤ 5082682318123^79*125000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40010401 125000000 5082682318123 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5540996789/10000000000 : ℝ)^95 ≤ (49165032844117/100000000000000 : ℝ)^79 := by
    have hnat : (5540996789 : ℕ)^95*100000000000000^79 ≤ 49165032844117^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5540996789 10000000000 49165032844117 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1600842519/5000000000 : ℝ), (-40010401/125000000 : ℝ), (5540996789/10000000000 : ℝ)] ![(12710777778371/50000000000000 : ℝ), (5082682318123/20000000000000 : ℝ), (49165032844117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1600842519/5000000000 : ℝ)|^95 ≤ (12710777778371/50000000000000 : ℝ)^79
        have hw : |(1600842519/5000000000 : ℝ)|=(1600842519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40010401/125000000 : ℝ)|^95 ≤ (5082682318123/20000000000000 : ℝ)^79
        have hw : |(-40010401/125000000 : ℝ)|=(40010401/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5540996789/10000000000 : ℝ)|^95 ≤ (49165032844117/100000000000000 : ℝ)^79
        have hw : |(5540996789/10000000000 : ℝ)|=(5540996789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s1_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5386331071/10000000000 : ℝ)*x 0 + (5355686777/10000000000 : ℝ)*x 1 + (-867323293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386331071/10000000000 : ℝ)^95 ≤ (47519447419971/100000000000000 : ℝ)^79 := by
    have hnat : (5386331071 : ℕ)^95*100000000000000^79 ≤ 47519447419971^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386331071 10000000000 47519447419971 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5355686777/10000000000 : ℝ)^95 ≤ (23597264695107/50000000000000 : ℝ)^79 := by
    have hnat : (5355686777 : ℕ)^95*50000000000000^79 ≤ 23597264695107^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355686777 10000000000 23597264695107 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (867323293/10000000000 : ℝ)^95 ≤ (5286023173469/100000000000000 : ℝ)^79 := by
    have hnat : (867323293 : ℕ)^95*100000000000000^79 ≤ 5286023173469^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867323293 10000000000 5286023173469 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386331071/10000000000 : ℝ), (5355686777/10000000000 : ℝ), (-867323293/10000000000 : ℝ)] ![(47519447419971/100000000000000 : ℝ), (23597264695107/50000000000000 : ℝ), (5286023173469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386331071/10000000000 : ℝ)|^95 ≤ (47519447419971/100000000000000 : ℝ)^79
        have hw : |(5386331071/10000000000 : ℝ)|=(5386331071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5355686777/10000000000 : ℝ)|^95 ≤ (23597264695107/50000000000000 : ℝ)^79
        have hw : |(5355686777/10000000000 : ℝ)|=(5355686777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-867323293/10000000000 : ℝ)|^95 ≤ (5286023173469/100000000000000 : ℝ)^79
        have hw : |(-867323293/10000000000 : ℝ)|=(867323293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329059_s1_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (830224237/2000000000 : ℝ)*x 0 + (1065435287/2500000000 : ℝ)*x 1 + (3613524747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (830224237/2000000000 : ℝ)^95 ≤ (17370080412691/50000000000000 : ℝ)^79 := by
    have hnat : (830224237 : ℕ)^95*50000000000000^79 ≤ 17370080412691^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830224237 2000000000 17370080412691 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065435287/2500000000 : ℝ)^95 ≤ (35856403551449/100000000000000 : ℝ)^79 := by
    have hnat : (1065435287 : ℕ)^95*100000000000000^79 ≤ 35856403551449^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065435287 2500000000 35856403551449 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3613524747/10000000000 : ℝ)^95 ≤ (29403435611049/100000000000000 : ℝ)^79 := by
    have hnat : (3613524747 : ℕ)^95*100000000000000^79 ≤ 29403435611049^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3613524747 10000000000 29403435611049 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(830224237/2000000000 : ℝ), (1065435287/2500000000 : ℝ), (3613524747/10000000000 : ℝ)] ![(17370080412691/50000000000000 : ℝ), (35856403551449/100000000000000 : ℝ), (29403435611049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(830224237/2000000000 : ℝ)|^95 ≤ (17370080412691/50000000000000 : ℝ)^79
        have hw : |(830224237/2000000000 : ℝ)|=(830224237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1065435287/2500000000 : ℝ)|^95 ≤ (35856403551449/100000000000000 : ℝ)^79
        have hw : |(1065435287/2500000000 : ℝ)|=(1065435287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3613524747/10000000000 : ℝ)|^95 ≤ (29403435611049/100000000000000 : ℝ)^79
        have hw : |(3613524747/10000000000 : ℝ)|=(3613524747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329059 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (160257/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-722998423/2500000000 : ℝ)*X 0 0+(578398557/2000000000 : ℝ)*X 0 1+(6083672123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2891993227/10000000000 : ℝ)*X 1 0+(-2891992067/10000000000 : ℝ)*X 1 1+(6083673141/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1438189423/5000000000 : ℝ)*X 0 0+(6286912969/10000000000 : ℝ)*X 0 1+(2668746987/10000000000 : ℝ)*X 0 2+(1438189423/5000000000 : ℝ)*X 1 0+(6286912969/10000000000 : ℝ)*X 1 1+(2668746987/10000000000 : ℝ)*X 1 2+(1438189423/5000000000 : ℝ)*X 2 0+(6286912969/10000000000 : ℝ)*X 2 1+(2668746987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-580273621/2500000000 : ℝ)*X 0 0+(163049303/2500000000 : ℝ)*X 0 1+(1643655433/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((466189943/2500000000 : ℝ)*X 1 0+(-1192036989/10000000000 : ℝ)*X 1 1+(513642291/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4131781993/10000000000 : ℝ)*X 2 0+(7029214053/10000000000 : ℝ)*X 2 1+(-1487759/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2058060829/10000000000 : ℝ)*X 0 0+(2000797579/2500000000 : ℝ)*X 0 1+(647259927/5000000000 : ℝ)*X 0 2+(2058060829/10000000000 : ℝ)*X 1 0+(2000797579/2500000000 : ℝ)*X 1 1+(647259927/5000000000 : ℝ)*X 1 2+(2058060829/10000000000 : ℝ)*X 2 0+(2000797579/2500000000 : ℝ)*X 2 1+(647259927/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-986764233/10000000000 : ℝ)*X 0 0+(519234509/2500000000 : ℝ)*X 0 1+(1639137341/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((36327781/400000000 : ℝ)*X 1 0+(-2143741787/10000000000 : ℝ)*X 1 1+(8195686719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((515185901/625000000 : ℝ)*X 2 0+(1351171879/5000000000 : ℝ)*X 2 1+(-880683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1653713067/2500000000 : ℝ)*X 0 0+(351401527/1000000000 : ℝ)*X 0 1+(156270023/1000000000 : ℝ)*X 0 2+(1653713067/2500000000 : ℝ)*X 1 0+(351401527/1000000000 : ℝ)*X 1 1+(156270023/1000000000 : ℝ)*X 1 2+(1653713067/2500000000 : ℝ)*X 2 0+(351401527/1000000000 : ℝ)*X 2 1+(156270023/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-4671359311/10000000000 : ℝ)*X 0 0+(45425541/200000000 : ℝ)*X 0 1+(2484969391/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((950999147/5000000000 : ℝ)*X 1 0+(-776021877/2500000000 : ℝ)*X 1 1+(6712348821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((8316712237/10000000000 : ℝ)*X 2 0+(2609542399/10000000000 : ℝ)*X 2 1+(-357409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((404682631/5000000000 : ℝ)*X 0 0+(8879946323/10000000000 : ℝ)*X 0 1+(51231793/400000000 : ℝ)*X 0 2+(404682631/5000000000 : ℝ)*X 1 0+(8879946323/10000000000 : ℝ)*X 1 1+(51231793/400000000 : ℝ)*X 1 2+(404682631/5000000000 : ℝ)*X 2 0+(8879946323/10000000000 : ℝ)*X 2 1+(51231793/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((60791/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60791/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (38892636516735441596001/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1214514675531/1000000000000 : ℝ)*(base7) + (1353/8000000000 : ℝ)*(base50) + (1498627247877/1000000000000 : ℝ)*(major_s0_0) + (1498627247877/1000000000000 : ℝ)*(major_s0_1) + (1498627247877/1000000000000 : ℝ)*(major_s0_2) + (72497/100000000000 : ℝ)*(sp_s0_0) + (1054991/125000000000 : ℝ)*(sp_s0_6) + (418611540559/250000000000 : ℝ)*(sp_s0_7) + (1674490978201/1000000000000 : ℝ)*(sp_s0_8) + (1674491187869/1000000000000 : ℝ)*(sp_s0_9) + (472112397227/250000000000 : ℝ)*(sp_s0_13) + (22150331/500000000000 : ℝ)*(sp_s0_14) + (52417/250000000000 : ℝ)*(sp_s0_15) + (3317437/100000000000 : ℝ)*(sp_s0_27) + (26959061107/40000000000 : ℝ)*(f.failure) + (1674491187869/1000000000000 : ℝ)*(f.sum) + (52800699/200000000000000000000 : ℝ)*base63 + (1421913306653523/10000000000000000000000000000 : ℝ)*base65 + (1578059287346477/10000000000000000000000000000 : ℝ)*base66 + (2283360476756189/10000000000000000000000000000 : ℝ)*base68 + (80010873150607/625000000000000000000000000 : ℝ)*base71 + (4344983475346477/10000000000000000000000000000 : ℝ)*base72 + (1014954167756189/10000000000000000000000000000 : ℝ)*base75 + (2759925882243811/10000000000000000000000000000 : ℝ)*base76 + (2354356947346477/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (23/1000000000000000 : ℝ)*base87 + (23/1000000000000000 : ℝ)*base89 + (23/1000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7571/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7571/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5051183929331420589987/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39973990791/125000000000 : ℝ)*(base5) + (121662698479/100000000000 : ℝ)*(base7) + (18687/40000000000 : ℝ)*(base13) + (123989024897/1000000000000 : ℝ)*(base60) + (302581790273/200000000000 : ℝ)*(major_s0_0) + (302581790273/200000000000 : ℝ)*(major_s0_1) + (302581790273/200000000000 : ℝ)*(major_s0_2) + (3747203/100000000000 : ℝ)*(sp_s0_8) + (169550467143/100000000000 : ℝ)*(sp_s0_14) + (423866912043/250000000000 : ℝ)*(sp_s0_15) + (1007539705317/500000000000 : ℝ)*(sp_s0_16) + (39430862153/25000000000 : ℝ)*(sp_s0_20) + (18403/1000000000000 : ℝ)*(sp_s0_22) + (2176543/10000000000 : ℝ)*(sp_s0_23) + (680399427659/1000000000000 : ℝ)*(f.failure) + (339101027721/200000000000 : ℝ)*(f.sum) + (284444303/1000000000000000000000 : ℝ)*base63 + (1107899531638327/2000000000000000000000000000 : ℝ)*base65 + (514383157638327/2000000000000000000000000000 : ℝ)*base67 + (1172024015341639/2000000000000000000000000000 : ℝ)*base69 + (23347746468543/125000000000000000000000000 : ℝ)*base71 + (526788345438327/2000000000000000000000000000 : ℝ)*base73 + (210078163458361/2000000000000000000000000000 : ℝ)*base75 + (569295829858361/2000000000000000000000000000 : ℝ)*base77 + (109511589838327/1000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (11151/25000000000000000 : ℝ)*base87 + (11151/25000000000000000 : ℝ)*base89 + (11151/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(5189/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(5189/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (27430344849541858847301/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (650929902763/1000000000000 : ℝ)*(base7) + (4817383/1000000000000 : ℝ)*(base8) + (1348589/1000000000000 : ℝ)*(base11) + (14641700927/40000000000 : ℝ)*(base44) + (828599019/7812500000 : ℝ)*(base50) + (1636829373259/1000000000000 : ℝ)*(major_s0_0) + (254157370017/200000000000 : ℝ)*(major_s0_1) + (1636829373259/1000000000000 : ℝ)*(major_s0_2) + (671099/62500000000 : ℝ)*(sp_s0_1) + (16313561/1000000000000 : ℝ)*(sp_s0_13) + (218980043943/100000000000 : ℝ)*(sp_s0_21) + (1823753344643/1000000000000 : ℝ)*(sp_s0_22) + (1094903302701/500000000000 : ℝ)*(sp_s0_23) + (1021001133693/1000000000000 : ℝ)*(sp_s0_27) + (368065033833/500000000000 : ℝ)*(f.failure) + (1094903302701/500000000000 : ℝ)*(f.sum) + (1492282557493659/5000000000000000000000000000 : ℝ)*base62 + (4889001397120541/10000000000000000000000000000 : ℝ)*base65 + (238898990479383/2000000000000000000000000000 : ℝ)*base67 + (2009535619098163/10000000000000000000000000000 : ℝ)*base68 + (69723309798831/625000000000000000000000000 : ℝ)*base70 + (794707053879459/10000000000000000000000000000 : ℝ)*base72 + (1406144748977831/2000000000000000000000000000 : ℝ)*base74 + (3236702861098163/10000000000000000000000000000 : ℝ)*base77 + (288639691282341/625000000000000000000000000 : ℝ)*base79 + (5137/12500000000000000 : ℝ)*base87 + (7363/12500000000000000 : ℝ)*base88 + (5137/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (60791/100000 : ℝ) ^ (93/16 : ℝ) ≤ (692589449717572717/12500000000000000000 : ℝ) := by
    have hpowers : (60791/100000 : ℝ)^93 ≤ (692589449717572717/12500000000000000000 : ℝ)^16 := by
      have hnat : (60791 : ℕ)^93*12500000000000000000^16 ≤ 692589449717572717^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60791 100000 692589449717572717 12500000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (60791/100000 : ℝ)) (X := (692589449717572717/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (13192589449717572717/12500000000000000000 : ℝ) ≤ (5046604348567191/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (13192589449717572717/12500000000000000000 : ℝ)^16 ≤ (5046604348567191/5000000000000000 : ℝ)^93 := by
      have hnat : (13192589449717572717 : ℕ)^16*5000000000000000^93 ≤ 5046604348567191^93*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13192589449717572717 12500000000000000000 5046604348567191 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5046604348567191/5000000000000000 : ℝ)) (X := (13192589449717572717/12500000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (6942589449717572717/6250000000000000000 : ℝ) ≤ (5091225107129613/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (6942589449717572717/6250000000000000000 : ℝ)^16 ≤ (5091225107129613/5000000000000000 : ℝ)^93 := by
      have hnat : (6942589449717572717 : ℕ)^16*5000000000000000^93 ≤ 5091225107129613^93*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6942589449717572717 6250000000000000000 5091225107129613 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5091225107129613/5000000000000000 : ℝ)) (X := (6942589449717572717/6250000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(46604348567191/3039550000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(22310379281211/1519775000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (60791/100000 : ℝ)) (alpha := (46604348567191/3039550000000000 : ℝ)) (beta := (22310379281211/1519775000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (60791/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(46604348567191/3039550000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(22310379281211/1519775000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (7571/12500 : ℝ) ^ (93/16 : ℝ) ≤ (2711807123181566413/50000000000000000000 : ℝ) := by
    have hpowers : (7571/12500 : ℝ)^93 ≤ (2711807123181566413/50000000000000000000 : ℝ)^16 := by
      have hnat : (7571 : ℕ)^93*50000000000000000000^16 ≤ 2711807123181566413^16*12500^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7571 12500 2711807123181566413 50000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7571/12500 : ℝ)) (X := (2711807123181566413/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (52711807123181566413/50000000000000000000 : ℝ) ≤ (5045640568954153/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (52711807123181566413/50000000000000000000 : ℝ)^16 ≤ (5045640568954153/5000000000000000 : ℝ)^93 := by
      have hnat : (52711807123181566413 : ℕ)^16*5000000000000000^93 ≤ 5045640568954153^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52711807123181566413 50000000000000000000 5045640568954153 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5045640568954153/5000000000000000 : ℝ)) (X := (52711807123181566413/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (27711807123181566413/25000000000000000000 : ℝ) ≤ (10178753472177133/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (27711807123181566413/25000000000000000000 : ℝ)^16 ≤ (10178753472177133/10000000000000000 : ℝ)^93 := by
      have hnat : (27711807123181566413 : ℕ)^16*10000000000000000^93 ≤ 10178753472177133^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27711807123181566413 25000000000000000000 10178753472177133 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10178753472177133/10000000000000000 : ℝ)) (X := (27711807123181566413/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(45640568954153/3028400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(87472334268827/6056800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (7571/12500 : ℝ)) (alpha := (45640568954153/3028400000000000 : ℝ)) (beta := (87472334268827/6056800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (7571/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(45640568954153/3028400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(87472334268827/6056800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (5189/12500 : ℝ) ^ (93/16 : ℝ) ≤ (37715025236036443/6250000000000000000 : ℝ) := by
    have hpowers : (5189/12500 : ℝ)^93 ≤ (37715025236036443/6250000000000000000 : ℝ)^16 := by
      have hnat : (5189 : ℕ)^93*6250000000000000000^16 ≤ 37715025236036443^16*12500^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5189 12500 37715025236036443 6250000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5189/12500 : ℝ)) (X := (37715025236036443/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (6287715025236036443/6250000000000000000 : ℝ) ≤ (1251294491312633/1250000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (6287715025236036443/6250000000000000000 : ℝ)^16 ≤ (1251294491312633/1250000000000000 : ℝ)^93 := by
      have hnat : (6287715025236036443 : ℕ)^16*1250000000000000^93 ≤ 1251294491312633^93*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6287715025236036443 6250000000000000000 1251294491312633 1250000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251294491312633/1250000000000000 : ℝ)) (X := (6287715025236036443/6250000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (3162715025236036443/3125000000000000000 : ℝ) ≤ (10020660557836183/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3162715025236036443/3125000000000000000 : ℝ)^16 ≤ (10020660557836183/10000000000000000 : ℝ)^93 := by
      have hnat : (3162715025236036443 : ℕ)^16*10000000000000000^93 ≤ 10020660557836183^93*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3162715025236036443 3125000000000000000 10020660557836183 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10020660557836183/10000000000000000 : ℝ)) (X := (3162715025236036443/3125000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1294491312633/518900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(10304627335119/4151200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (5189/12500 : ℝ)) (alpha := (1294491312633/518900000000000 : ℝ)) (beta := (10304627335119/4151200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (5189/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1294491312633/518900000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(10304627335119/4151200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-320254717/1000000000 : ℝ)*X 0 0+(1600848847/5000000000 : ℝ)*X 0 1+(2769725327/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1600842519/5000000000 : ℝ)*X 1 0+(-40010401/125000000 : ℝ)*X 1 1+(5540996789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5386331071/10000000000 : ℝ)*X 2 0+(5355686777/10000000000 : ℝ)*X 2 1+(-867323293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((830224237/2000000000 : ℝ)*X 0 0+(1065435287/2500000000 : ℝ)*X 0 1+(3613524747/10000000000 : ℝ)*X 0 2+(830224237/2000000000 : ℝ)*X 1 0+(1065435287/2500000000 : ℝ)*X 1 1+(3613524747/10000000000 : ℝ)*X 1 2+(830224237/2000000000 : ℝ)*X 2 0+(1065435287/2500000000 : ℝ)*X 2 1+(3613524747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329059_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-129267/12500 : ℝ) < ((-55589/25000 : ℝ)*P 0+(-55589/25000 : ℝ)*P 1+(-55589/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-129267/12500 : ℝ) < (-245010255518823806407710968105624667/23882303019290000000000000000000000 : ℝ) := by norm_num
    linear_combination (450397/1000000000000 : ℝ)*(base5) + (158877/1000000000000 : ℝ)*(base7) + (269489/1000000000000 : ℝ)*(base8) + (331773/1000000000000 : ℝ)*(base11) + (56911/100000000000 : ℝ)*(base19) + (127651/250000000000 : ℝ)*(base21) + (17487/500000000000 : ℝ)*(base29) + (44251496957/62500000000 : ℝ)*(base60) + (55589/25000 : ℝ)*(major_s1_0) + (55589/25000 : ℝ)*(major_s1_1) + (55589/25000 : ℝ)*(major_s1_2) + (3419689831439/1000000000000 : ℝ)*(sp_s1_0) + (427461232949/125000000000 : ℝ)*(sp_s1_1) + (683938074499/200000000000 : ℝ)*(sp_s1_2) + (499999836753/500000000000 : ℝ)*(sp_s1_6) + (1709845216351/500000000000 : ℝ)*(f.sum) + (15508683124508731/19642959500000000000000000000 : ℝ)*base62 + (5161087155647/25945000000000000000000000 : ℝ)*base65 + (606085223719/9463750000000000000000000 : ℝ)*base67 + (13923953489517/25945000000000000000000000 : ℝ)*base68 + (81540122247087809/394305623750000000000000000000 : ℝ)*base70 + (5583534612437/60791000000000000000000000 : ℝ)*base72 + (1914705790421/15142000000000000000000000 : ℝ)*base74 + (218152137629127/607910000000000000000000000 : ℝ)*base77 + (289246065523367967/4602486610000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p029_b029 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 59 ≤ c.val) (hhi : c.val < 60)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=59 := by omega
  rcases hc with rfl
  · exact collision_c329059 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 59 ≤ c.val) (hhi : c.val < 60)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b029 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p004_b032
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:25:38.290468+00:00
-- url     : https://prove2.me/submissions/ac292132-ce38-43d0-9dba-4caaaa6149f3

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
theorem collision_support_c304071_s0_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (924019199/2500000000 : ℝ)*x 0 + (565306469/1000000000 : ℝ)*x 1 + (3579641281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (924019199/2500000000 : ℝ)^133 ≤ (13482102969617/50000000000000 : ℝ)^101 := by
    have hnat : (924019199 : ℕ)^133*50000000000000^101 ≤ 13482102969617^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924019199 2500000000 13482102969617 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565306469/1000000000 : ℝ)^133 ≤ (9436906661177/20000000000000 : ℝ)^101 := by
    have hnat : (565306469 : ℕ)^133*20000000000000^101 ≤ 9436906661177^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565306469 1000000000 9436906661177 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3579641281/10000000000 : ℝ)^133 ≤ (1615703796367/6250000000000 : ℝ)^101 := by
    have hnat : (3579641281 : ℕ)^133*6250000000000^101 ≤ 1615703796367^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3579641281 10000000000 1615703796367 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(924019199/2500000000 : ℝ), (565306469/1000000000 : ℝ), (3579641281/10000000000 : ℝ)] ![(13482102969617/50000000000000 : ℝ), (9436906661177/20000000000000 : ℝ), (1615703796367/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(924019199/2500000000 : ℝ)|^133 ≤ (13482102969617/50000000000000 : ℝ)^101
        have hw : |(924019199/2500000000 : ℝ)|=(924019199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565306469/1000000000 : ℝ)|^133 ≤ (9436906661177/20000000000000 : ℝ)^101
        have hw : |(565306469/1000000000 : ℝ)|=(565306469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3579641281/10000000000 : ℝ)|^133 ≤ (1615703796367/6250000000000 : ℝ)^101
        have hw : |(3579641281/10000000000 : ℝ)|=(3579641281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s0_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (450033903/625000000 : ℝ)*x 0 + (-3752768549/10000000000 : ℝ)*x 1 + (-353223489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450033903/625000000 : ℝ)^133 ≤ (64889435477531/100000000000000 : ℝ)^101 := by
    have hnat : (450033903 : ℕ)^133*100000000000000^101 ≤ 64889435477531^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450033903 625000000 64889435477531 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3752768549/10000000000 : ℝ)^133 ≤ (13755074364597/50000000000000 : ℝ)^101 := by
    have hnat : (3752768549 : ℕ)^133*50000000000000^101 ≤ 13755074364597^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3752768549 10000000000 13755074364597 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (353223489/2500000000 : ℝ)^133 ≤ (7600415781279/100000000000000 : ℝ)^101 := by
    have hnat : (353223489 : ℕ)^133*100000000000000^101 ≤ 7600415781279^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353223489 2500000000 7600415781279 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(450033903/625000000 : ℝ), (-3752768549/10000000000 : ℝ), (-353223489/2500000000 : ℝ)] ![(64889435477531/100000000000000 : ℝ), (13755074364597/50000000000000 : ℝ), (7600415781279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(450033903/625000000 : ℝ)|^133 ≤ (64889435477531/100000000000000 : ℝ)^101
        have hw : |(450033903/625000000 : ℝ)|=(450033903/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3752768549/10000000000 : ℝ)|^133 ≤ (13755074364597/50000000000000 : ℝ)^101
        have hw : |(-3752768549/10000000000 : ℝ)|=(3752768549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-353223489/2500000000 : ℝ)|^133 ≤ (7600415781279/100000000000000 : ℝ)^101
        have hw : |(-353223489/2500000000 : ℝ)|=(353223489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s0_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-112013607/10000000000 : ℝ)*x 0 + (-102098837/500000000 : ℝ)*x 1 + (1128344463/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112013607/10000000000 : ℝ)^133 ≤ (16869335603/6250000000000 : ℝ)^101 := by
    have hnat : (112013607 : ℕ)^133*6250000000000^101 ≤ 16869335603^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112013607 10000000000 16869335603 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102098837/500000000 : ℝ)^133 ≤ (12343917813317/100000000000000 : ℝ)^101 := by
    have hnat : (102098837 : ℕ)^133*100000000000000^101 ≤ 12343917813317^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102098837 500000000 12343917813317 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128344463/1250000000 : ℝ)^133 ≤ (87386172808813/100000000000000 : ℝ)^101 := by
    have hnat : (1128344463 : ℕ)^133*100000000000000^101 ≤ 87386172808813^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128344463 1250000000 87386172808813 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-112013607/10000000000 : ℝ), (-102098837/500000000 : ℝ), (1128344463/1250000000 : ℝ)] ![(16869335603/6250000000000 : ℝ), (12343917813317/100000000000000 : ℝ), (87386172808813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-112013607/10000000000 : ℝ)|^133 ≤ (16869335603/6250000000000 : ℝ)^101
        have hw : |(-112013607/10000000000 : ℝ)|=(112013607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102098837/500000000 : ℝ)|^133 ≤ (12343917813317/100000000000000 : ℝ)^101
        have hw : |(-102098837/500000000 : ℝ)|=(102098837/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1128344463/1250000000 : ℝ)|^133 ≤ (87386172808813/100000000000000 : ℝ)^101
        have hw : |(1128344463/1250000000 : ℝ)|=(1128344463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s0_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-747227571/2000000000 : ℝ)*x 0 + (-234917221/400000000 : ℝ)*x 1 + (3279365687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (747227571/2000000000 : ℝ)^133 ≤ (27349722086987/100000000000000 : ℝ)^101 := by
    have hnat : (747227571 : ℕ)^133*100000000000000^101 ≤ 27349722086987^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747227571 2000000000 27349722086987 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (234917221/400000000 : ℝ)^133 ≤ (24807943545319/50000000000000 : ℝ)^101 := by
    have hnat : (234917221 : ℕ)^133*50000000000000^101 ≤ 24807943545319^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234917221 400000000 24807943545319 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3279365687/10000000000 : ℝ)^133 ≤ (4606878160243/20000000000000 : ℝ)^101 := by
    have hnat : (3279365687 : ℕ)^133*20000000000000^101 ≤ 4606878160243^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3279365687 10000000000 4606878160243 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-747227571/2000000000 : ℝ), (-234917221/400000000 : ℝ), (3279365687/10000000000 : ℝ)] ![(27349722086987/100000000000000 : ℝ), (24807943545319/50000000000000 : ℝ), (4606878160243/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-747227571/2000000000 : ℝ)|^133 ≤ (27349722086987/100000000000000 : ℝ)^101
        have hw : |(-747227571/2000000000 : ℝ)|=(747227571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-234917221/400000000 : ℝ)|^133 ≤ (24807943545319/50000000000000 : ℝ)^101
        have hw : |(-234917221/400000000 : ℝ)|=(234917221/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3279365687/10000000000 : ℝ)|^133 ≤ (4606878160243/20000000000000 : ℝ)^101
        have hw : |(3279365687/10000000000 : ℝ)|=(3279365687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s0_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2607723657/10000000000 : ℝ)*x 0 + (716260613/1000000000 : ℝ)*x 1 + (1389736723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2607723657/10000000000 : ℝ)^133 ≤ (17033925230441/100000000000000 : ℝ)^101 := by
    have hnat : (2607723657 : ℕ)^133*100000000000000^101 ≤ 17033925230441^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607723657 10000000000 17033925230441 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (716260613/1000000000 : ℝ)^133 ≤ (64439623343147/100000000000000 : ℝ)^101 := by
    have hnat : (716260613 : ℕ)^133*100000000000000^101 ≤ 64439623343147^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      716260613 1000000000 64439623343147 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1389736723/5000000000 : ℝ)^133 ≤ (9263225701567/50000000000000 : ℝ)^101 := by
    have hnat : (1389736723 : ℕ)^133*50000000000000^101 ≤ 9263225701567^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389736723 5000000000 9263225701567 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2607723657/10000000000 : ℝ), (716260613/1000000000 : ℝ), (1389736723/5000000000 : ℝ)] ![(17033925230441/100000000000000 : ℝ), (64439623343147/100000000000000 : ℝ), (9263225701567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2607723657/10000000000 : ℝ)|^133 ≤ (17033925230441/100000000000000 : ℝ)^101
        have hw : |(2607723657/10000000000 : ℝ)|=(2607723657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(716260613/1000000000 : ℝ)|^133 ≤ (64439623343147/100000000000000 : ℝ)^101
        have hw : |(716260613/1000000000 : ℝ)|=(716260613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1389736723/5000000000 : ℝ)|^133 ≤ (9263225701567/50000000000000 : ℝ)^101
        have hw : |(1389736723/5000000000 : ℝ)|=(1389736723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s0_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8209923793/10000000000 : ℝ)*x 0 + (-1625147193/5000000000 : ℝ)*x 1 + (-28021469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8209923793/10000000000 : ℝ)^133 ≤ (77125687249429/100000000000000 : ℝ)^101 := by
    have hnat : (8209923793 : ℕ)^133*100000000000000^101 ≤ 77125687249429^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8209923793 10000000000 77125687249429 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1625147193/5000000000 : ℝ)^133 ≤ (4553174974607/20000000000000 : ℝ)^101 := by
    have hnat : (1625147193 : ℕ)^133*20000000000000^101 ≤ 4553174974607^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625147193 5000000000 4553174974607 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28021469/5000000000 : ℝ)^133 ≤ (108437870457/100000000000000 : ℝ)^101 := by
    have hnat : (28021469 : ℕ)^133*100000000000000^101 ≤ 108437870457^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28021469 5000000000 108437870457 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8209923793/10000000000 : ℝ), (-1625147193/5000000000 : ℝ), (-28021469/5000000000 : ℝ)] ![(77125687249429/100000000000000 : ℝ), (4553174974607/20000000000000 : ℝ), (108437870457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8209923793/10000000000 : ℝ)|^133 ≤ (77125687249429/100000000000000 : ℝ)^101
        have hw : |(8209923793/10000000000 : ℝ)|=(8209923793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1625147193/5000000000 : ℝ)|^133 ≤ (4553174974607/20000000000000 : ℝ)^101
        have hw : |(-1625147193/5000000000 : ℝ)|=(1625147193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28021469/5000000000 : ℝ)|^133 ≤ (108437870457/100000000000000 : ℝ)^101
        have hw : |(-28021469/5000000000 : ℝ)|=(28021469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s0_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-114140051/5000000000 : ℝ)*x 0 + (-54209327/400000000 : ℝ)*x 1 + (2348856731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114140051/5000000000 : ℝ)^133 ≤ (137850620531/20000000000000 : ℝ)^101 := by
    have hnat : (114140051 : ℕ)^133*20000000000000^101 ≤ 137850620531^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114140051 5000000000 137850620531 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54209327/400000000 : ℝ)^133 ≤ (7194631695753/100000000000000 : ℝ)^101 := by
    have hnat : (54209327 : ℕ)^133*100000000000000^101 ≤ 7194631695753^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54209327 400000000 7194631695753 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2348856731/2500000000 : ℝ)^133 ≤ (46058057592871/50000000000000 : ℝ)^101 := by
    have hnat : (2348856731 : ℕ)^133*50000000000000^101 ≤ 46058057592871^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2348856731 2500000000 46058057592871 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-114140051/5000000000 : ℝ), (-54209327/400000000 : ℝ), (2348856731/2500000000 : ℝ)] ![(137850620531/20000000000000 : ℝ), (7194631695753/100000000000000 : ℝ), (46058057592871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-114140051/5000000000 : ℝ)|^133 ≤ (137850620531/20000000000000 : ℝ)^101
        have hw : |(-114140051/5000000000 : ℝ)|=(114140051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54209327/400000000 : ℝ)|^133 ≤ (7194631695753/100000000000000 : ℝ)^101
        have hw : |(-54209327/400000000 : ℝ)|=(54209327/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2348856731/2500000000 : ℝ)|^133 ≤ (46058057592871/50000000000000 : ℝ)^101
        have hw : |(2348856731/2500000000 : ℝ)|=(2348856731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s0_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3584155561/10000000000 : ℝ)*x 0 + (-274955159/1000000000 : ℝ)*x 1 + (803063321/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3584155561/10000000000 : ℝ)^133 ≤ (161838745781/625000000000 : ℝ)^101 := by
    have hnat : (3584155561 : ℕ)^133*625000000000^101 ≤ 161838745781^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3584155561 10000000000 161838745781 625000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274955159/1000000000 : ℝ)^133 ≤ (18264267873611/100000000000000 : ℝ)^101 := by
    have hnat : (274955159 : ℕ)^133*100000000000000^101 ≤ 18264267873611^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274955159 1000000000 18264267873611 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (803063321/1250000000 : ℝ)^133 ≤ (11168306558067/20000000000000 : ℝ)^101 := by
    have hnat : (803063321 : ℕ)^133*20000000000000^101 ≤ 11168306558067^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803063321 1250000000 11168306558067 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3584155561/10000000000 : ℝ), (-274955159/1000000000 : ℝ), (803063321/1250000000 : ℝ)] ![(161838745781/625000000000 : ℝ), (18264267873611/100000000000000 : ℝ), (11168306558067/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3584155561/10000000000 : ℝ)|^133 ≤ (161838745781/625000000000 : ℝ)^101
        have hw : |(-3584155561/10000000000 : ℝ)|=(3584155561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-274955159/1000000000 : ℝ)|^133 ≤ (18264267873611/100000000000000 : ℝ)^101
        have hw : |(-274955159/1000000000 : ℝ)|=(274955159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(803063321/1250000000 : ℝ)|^133 ≤ (11168306558067/20000000000000 : ℝ)^101
        have hw : |(803063321/1250000000 : ℝ)|=(803063321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s0_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6827901219/10000000000 : ℝ)*x 0 + (713135221/2000000000 : ℝ)*x 1 + (443931687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6827901219/10000000000 : ℝ)^133 ≤ (30252005992717/50000000000000 : ℝ)^101 := by
    have hnat : (6827901219 : ℕ)^133*50000000000000^101 ≤ 30252005992717^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6827901219 10000000000 30252005992717 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (713135221/2000000000 : ℝ)^133 ≤ (12859268262061/50000000000000 : ℝ)^101 := by
    have hnat : (713135221 : ℕ)^133*50000000000000^101 ≤ 12859268262061^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713135221 2000000000 12859268262061 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443931687/2000000000 : ℝ)^133 ≤ (13777451473567/100000000000000 : ℝ)^101 := by
    have hnat : (443931687 : ℕ)^133*100000000000000^101 ≤ 13777451473567^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443931687 2000000000 13777451473567 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6827901219/10000000000 : ℝ), (713135221/2000000000 : ℝ), (443931687/2000000000 : ℝ)] ![(30252005992717/50000000000000 : ℝ), (12859268262061/50000000000000 : ℝ), (13777451473567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6827901219/10000000000 : ℝ)|^133 ≤ (30252005992717/50000000000000 : ℝ)^101
        have hw : |(6827901219/10000000000 : ℝ)|=(6827901219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(713135221/2000000000 : ℝ)|^133 ≤ (12859268262061/50000000000000 : ℝ)^101
        have hw : |(713135221/2000000000 : ℝ)|=(713135221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(443931687/2000000000 : ℝ)|^133 ≤ (13777451473567/100000000000000 : ℝ)^101
        have hw : |(443931687/2000000000 : ℝ)|=(443931687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s0_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8898574679/10000000000 : ℝ)*x 0 + (-1827670463/10000000000 : ℝ)*x 1 + (-797183857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8898574679/10000000000 : ℝ)^133 ≤ (17151162348473/20000000000000 : ℝ)^101 := by
    have hnat : (8898574679 : ℕ)^133*20000000000000^101 ≤ 17151162348473^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8898574679 10000000000 17151162348473 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1827670463/10000000000 : ℝ)^133 ≤ (5333517995587/50000000000000 : ℝ)^101 := by
    have hnat : (1827670463 : ℕ)^133*50000000000000^101 ≤ 5333517995587^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827670463 10000000000 5333517995587 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (797183857/10000000000 : ℝ)^133 ≤ (3577152250483/100000000000000 : ℝ)^101 := by
    have hnat : (797183857 : ℕ)^133*100000000000000^101 ≤ 3577152250483^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797183857 10000000000 3577152250483 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8898574679/10000000000 : ℝ), (-1827670463/10000000000 : ℝ), (-797183857/10000000000 : ℝ)] ![(17151162348473/20000000000000 : ℝ), (5333517995587/50000000000000 : ℝ), (3577152250483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8898574679/10000000000 : ℝ)|^133 ≤ (17151162348473/20000000000000 : ℝ)^101
        have hw : |(8898574679/10000000000 : ℝ)|=(8898574679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1827670463/10000000000 : ℝ)|^133 ≤ (5333517995587/50000000000000 : ℝ)^101
        have hw : |(-1827670463/10000000000 : ℝ)|=(1827670463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-797183857/10000000000 : ℝ)|^133 ≤ (3577152250483/100000000000000 : ℝ)^101
        have hw : |(-797183857/10000000000 : ℝ)|=(797183857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s0_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-5034679/1250000000 : ℝ)*x 0 + (-1534153853/10000000000 : ℝ)*x 1 + (1868896799/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5034679/1250000000 : ℝ)^133 ≤ (17547266511/25000000000000 : ℝ)^101 := by
    have hnat : (5034679 : ℕ)^133*25000000000000^101 ≤ 17547266511^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5034679 1250000000 17547266511 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1534153853/10000000000 : ℝ)^133 ≤ (8470838331649/100000000000000 : ℝ)^101 := by
    have hnat : (1534153853 : ℕ)^133*100000000000000^101 ≤ 8470838331649^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1534153853 10000000000 8470838331649 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1868896799/2000000000 : ℝ)^133 ≤ (9145897259477/10000000000000 : ℝ)^101 := by
    have hnat : (1868896799 : ℕ)^133*10000000000000^101 ≤ 9145897259477^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868896799 2000000000 9145897259477 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5034679/1250000000 : ℝ), (-1534153853/10000000000 : ℝ), (1868896799/2000000000 : ℝ)] ![(17547266511/25000000000000 : ℝ), (8470838331649/100000000000000 : ℝ), (9145897259477/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5034679/1250000000 : ℝ)|^133 ≤ (17547266511/25000000000000 : ℝ)^101
        have hw : |(-5034679/1250000000 : ℝ)|=(5034679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1534153853/10000000000 : ℝ)|^133 ≤ (8470838331649/100000000000000 : ℝ)^101
        have hw : |(-1534153853/10000000000 : ℝ)|=(1534153853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1868896799/2000000000 : ℝ)|^133 ≤ (9145897259477/10000000000000 : ℝ)^101
        have hw : |(1868896799/2000000000 : ℝ)|=(1868896799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s0_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-750966029/2000000000 : ℝ)*x 0 + (-1153432289/2500000000 : ℝ)*x 1 + (579774067/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (750966029/2000000000 : ℝ)^133 ≤ (13765025732471/50000000000000 : ℝ)^101 := by
    have hnat : (750966029 : ℕ)^133*50000000000000^101 ≤ 13765025732471^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750966029 2000000000 13765025732471 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1153432289/2500000000 : ℝ)^133 ≤ (18054404178163/50000000000000 : ℝ)^101 := by
    have hnat : (1153432289 : ℕ)^133*50000000000000^101 ≤ 18054404178163^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153432289 2500000000 18054404178163 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (579774067/1250000000 : ℝ)^133 ≤ (3636114015893/10000000000000 : ℝ)^101 := by
    have hnat : (579774067 : ℕ)^133*10000000000000^101 ≤ 3636114015893^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579774067 1250000000 3636114015893 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-750966029/2000000000 : ℝ), (-1153432289/2500000000 : ℝ), (579774067/1250000000 : ℝ)] ![(13765025732471/50000000000000 : ℝ), (18054404178163/50000000000000 : ℝ), (3636114015893/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-750966029/2000000000 : ℝ)|^133 ≤ (13765025732471/50000000000000 : ℝ)^101
        have hw : |(-750966029/2000000000 : ℝ)|=(750966029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1153432289/2500000000 : ℝ)|^133 ≤ (18054404178163/50000000000000 : ℝ)^101
        have hw : |(-1153432289/2500000000 : ℝ)|=(1153432289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(579774067/1250000000 : ℝ)|^133 ≤ (3636114015893/10000000000000 : ℝ)^101
        have hw : |(579774067/1250000000 : ℝ)|=(579774067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s0_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2865231199/10000000000 : ℝ)*x 0 + (6177863521/10000000000 : ℝ)*x 1 + (235655711/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2865231199/10000000000 : ℝ)^133 ≤ (19282824850347/100000000000000 : ℝ)^101 := by
    have hnat : (2865231199 : ℕ)^133*100000000000000^101 ≤ 19282824850347^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2865231199 10000000000 19282824850347 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6177863521/10000000000 : ℝ)^133 ≤ (53035816515917/100000000000000 : ℝ)^101 := by
    have hnat : (6177863521 : ℕ)^133*100000000000000^101 ≤ 53035816515917^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6177863521 10000000000 53035816515917 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235655711/625000000 : ℝ)^133 ≤ (6920339656381/25000000000000 : ℝ)^101 := by
    have hnat : (235655711 : ℕ)^133*25000000000000^101 ≤ 6920339656381^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235655711 625000000 6920339656381 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2865231199/10000000000 : ℝ), (6177863521/10000000000 : ℝ), (235655711/625000000 : ℝ)] ![(19282824850347/100000000000000 : ℝ), (53035816515917/100000000000000 : ℝ), (6920339656381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2865231199/10000000000 : ℝ)|^133 ≤ (19282824850347/100000000000000 : ℝ)^101
        have hw : |(2865231199/10000000000 : ℝ)|=(2865231199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6177863521/10000000000 : ℝ)|^133 ≤ (53035816515917/100000000000000 : ℝ)^101
        have hw : |(6177863521/10000000000 : ℝ)|=(6177863521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(235655711/625000000 : ℝ)|^133 ≤ (6920339656381/25000000000000 : ℝ)^101
        have hw : |(235655711/625000000 : ℝ)|=(235655711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s0_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (121032421/156250000 : ℝ)*x 0 + (-2823706269/10000000000 : ℝ)*x 1 + (-52907839/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121032421/156250000 : ℝ)^133 ≤ (71439640609733/100000000000000 : ℝ)^101 := by
    have hnat : (121032421 : ℕ)^133*100000000000000^101 ≤ 71439640609733^101*156250000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121032421 156250000 71439640609733 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2823706269/10000000000 : ℝ)^133 ≤ (9457835278351/50000000000000 : ℝ)^101 := by
    have hnat : (2823706269 : ℕ)^133*50000000000000^101 ≤ 9457835278351^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2823706269 10000000000 9457835278351 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52907839/312500000 : ℝ)^133 ≤ (4822344410037/50000000000000 : ℝ)^101 := by
    have hnat : (52907839 : ℕ)^133*50000000000000^101 ≤ 4822344410037^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52907839 312500000 4822344410037 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(121032421/156250000 : ℝ), (-2823706269/10000000000 : ℝ), (-52907839/312500000 : ℝ)] ![(71439640609733/100000000000000 : ℝ), (9457835278351/50000000000000 : ℝ), (4822344410037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(121032421/156250000 : ℝ)|^133 ≤ (71439640609733/100000000000000 : ℝ)^101
        have hw : |(121032421/156250000 : ℝ)|=(121032421/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2823706269/10000000000 : ℝ)|^133 ≤ (9457835278351/50000000000000 : ℝ)^101
        have hw : |(-2823706269/10000000000 : ℝ)|=(2823706269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52907839/312500000 : ℝ)|^133 ≤ (4822344410037/50000000000000 : ℝ)^101
        have hw : |(-52907839/312500000 : ℝ)|=(52907839/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s1_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3565172507/10000000000 : ℝ)*x 0 + (-2082790693/5000000000 : ℝ)*x 1 + (2621185823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3565172507/10000000000 : ℝ)^133 ≤ (2571375343021/10000000000000 : ℝ)^101 := by
    have hnat : (3565172507 : ℕ)^133*10000000000000^101 ≤ 2571375343021^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3565172507 10000000000 2571375343021 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082790693/5000000000 : ℝ)^133 ≤ (789072340959/2500000000000 : ℝ)^101 := by
    have hnat : (2082790693 : ℕ)^133*2500000000000^101 ≤ 789072340959^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082790693 5000000000 789072340959 2500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621185823/5000000000 : ℝ)^133 ≤ (2670209557621/6250000000000 : ℝ)^101 := by
    have hnat : (2621185823 : ℕ)^133*6250000000000^101 ≤ 2670209557621^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621185823 5000000000 2670209557621 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3565172507/10000000000 : ℝ), (-2082790693/5000000000 : ℝ), (2621185823/5000000000 : ℝ)] ![(2571375343021/10000000000000 : ℝ), (789072340959/2500000000000 : ℝ), (2670209557621/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3565172507/10000000000 : ℝ)|^133 ≤ (2571375343021/10000000000000 : ℝ)^101
        have hw : |(-3565172507/10000000000 : ℝ)|=(3565172507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2082790693/5000000000 : ℝ)|^133 ≤ (789072340959/2500000000000 : ℝ)^101
        have hw : |(-2082790693/5000000000 : ℝ)|=(2082790693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621185823/5000000000 : ℝ)|^133 ≤ (2670209557621/6250000000000 : ℝ)^101
        have hw : |(2621185823/5000000000 : ℝ)|=(2621185823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s1_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (269874999/625000000 : ℝ)*x 0 + (2554354737/5000000000 : ℝ)*x 1 + (3554539437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269874999/625000000 : ℝ)^133 ≤ (33092427052711/100000000000000 : ℝ)^101 := by
    have hnat : (269874999 : ℕ)^133*100000000000000^101 ≤ 33092427052711^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269874999 625000000 33092427052711 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2554354737/5000000000 : ℝ)^133 ≤ (20647380357019/50000000000000 : ℝ)^101 := by
    have hnat : (2554354737 : ℕ)^133*50000000000000^101 ≤ 20647380357019^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2554354737 5000000000 20647380357019 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3554539437/10000000000 : ℝ)^133 ≤ (25612812224927/100000000000000 : ℝ)^101 := by
    have hnat : (3554539437 : ℕ)^133*100000000000000^101 ≤ 25612812224927^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3554539437 10000000000 25612812224927 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269874999/625000000 : ℝ), (2554354737/5000000000 : ℝ), (3554539437/10000000000 : ℝ)] ![(33092427052711/100000000000000 : ℝ), (20647380357019/50000000000000 : ℝ), (25612812224927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269874999/625000000 : ℝ)|^133 ≤ (33092427052711/100000000000000 : ℝ)^101
        have hw : |(269874999/625000000 : ℝ)|=(269874999/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2554354737/5000000000 : ℝ)|^133 ≤ (20647380357019/50000000000000 : ℝ)^101
        have hw : |(2554354737/5000000000 : ℝ)|=(2554354737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3554539437/10000000000 : ℝ)|^133 ≤ (25612812224927/100000000000000 : ℝ)^101
        have hw : |(3554539437/10000000000 : ℝ)|=(3554539437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s1_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5875419267/10000000000 : ℝ)*x 0 + (-2109408409/5000000000 : ℝ)*x 1 + (-687302779/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5875419267/10000000000 : ℝ)^133 ≤ (12410893989523/25000000000000 : ℝ)^101 := by
    have hnat : (5875419267 : ℕ)^133*25000000000000^101 ≤ 12410893989523^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5875419267 10000000000 12410893989523 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109408409/5000000000 : ℝ)^133 ≤ (6419026859951/20000000000000 : ℝ)^101 := by
    have hnat : (2109408409 : ℕ)^133*20000000000000^101 ≤ 6419026859951^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109408409 5000000000 6419026859951 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (687302779/2500000000 : ℝ)^133 ≤ (18261289726849/100000000000000 : ℝ)^101 := by
    have hnat : (687302779 : ℕ)^133*100000000000000^101 ≤ 18261289726849^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687302779 2500000000 18261289726849 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5875419267/10000000000 : ℝ), (-2109408409/5000000000 : ℝ), (-687302779/2500000000 : ℝ)] ![(12410893989523/25000000000000 : ℝ), (6419026859951/20000000000000 : ℝ), (18261289726849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5875419267/10000000000 : ℝ)|^133 ≤ (12410893989523/25000000000000 : ℝ)^101
        have hw : |(5875419267/10000000000 : ℝ)|=(5875419267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109408409/5000000000 : ℝ)|^133 ≤ (6419026859951/20000000000000 : ℝ)^101
        have hw : |(-2109408409/5000000000 : ℝ)|=(2109408409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-687302779/2500000000 : ℝ)|^133 ≤ (18261289726849/100000000000000 : ℝ)^101
        have hw : |(-687302779/2500000000 : ℝ)|=(687302779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304071_s1_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (532955629/2500000000 : ℝ)*x 0 + (-2646519551/10000000000 : ℝ)*x 1 + (7591432977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532955629/2500000000 : ℝ)^133 ≤ (2612811652429/20000000000000 : ℝ)^101 := by
    have hnat : (532955629 : ℕ)^133*20000000000000^101 ≤ 2612811652429^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532955629 2500000000 2612811652429 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2646519551/10000000000 : ℝ)^133 ≤ (17368419054891/100000000000000 : ℝ)^101 := by
    have hnat : (2646519551 : ℕ)^133*100000000000000^101 ≤ 17368419054891^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646519551 10000000000 17368419054891 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7591432977/10000000000 : ℝ)^133 ≤ (34783761334191/50000000000000 : ℝ)^101 := by
    have hnat : (7591432977 : ℕ)^133*50000000000000^101 ≤ 34783761334191^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7591432977 10000000000 34783761334191 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532955629/2500000000 : ℝ), (-2646519551/10000000000 : ℝ), (7591432977/10000000000 : ℝ)] ![(2612811652429/20000000000000 : ℝ), (17368419054891/100000000000000 : ℝ), (34783761334191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532955629/2500000000 : ℝ)|^133 ≤ (2612811652429/20000000000000 : ℝ)^101
        have hw : |(532955629/2500000000 : ℝ)|=(532955629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2646519551/10000000000 : ℝ)|^133 ≤ (17368419054891/100000000000000 : ℝ)^101
        have hw : |(-2646519551/10000000000 : ℝ)|=(2646519551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7591432977/10000000000 : ℝ)|^133 ≤ (34783761334191/50000000000000 : ℝ)^101
        have hw : |(7591432977/10000000000 : ℝ)|=(7591432977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304071 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((924019199/2500000000 : ℝ)*X 1 0+(565306469/1000000000 : ℝ)*X 1 1+(3579641281/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((450033903/625000000 : ℝ)*X 2 0+(-3752768549/10000000000 : ℝ)*X 2 1+(-353223489/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((-112013607/10000000000 : ℝ)*X 0 0+(-102098837/500000000 : ℝ)*X 0 1+(1128344463/1250000000 : ℝ)*X 0 2+(-112013607/10000000000 : ℝ)*X 1 0+(-102098837/500000000 : ℝ)*X 1 1+(1128344463/1250000000 : ℝ)*X 1 2+(-112013607/10000000000 : ℝ)*X 2 0+(-102098837/500000000 : ℝ)*X 2 1+(1128344463/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-747227571/2000000000 : ℝ)*X 0 0+(-234917221/400000000 : ℝ)*X 0 1+(3279365687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2607723657/10000000000 : ℝ)*X 1 0+(716260613/1000000000 : ℝ)*X 1 1+(1389736723/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((8209923793/10000000000 : ℝ)*X 2 0+(-1625147193/5000000000 : ℝ)*X 2 1+(-28021469/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-114140051/5000000000 : ℝ)*X 0 0+(-54209327/400000000 : ℝ)*X 0 1+(2348856731/2500000000 : ℝ)*X 0 2+(-114140051/5000000000 : ℝ)*X 1 0+(-54209327/400000000 : ℝ)*X 1 1+(2348856731/2500000000 : ℝ)*X 1 2+(-114140051/5000000000 : ℝ)*X 2 0+(-54209327/400000000 : ℝ)*X 2 1+(2348856731/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-3584155561/10000000000 : ℝ)*X 0 0+(-274955159/1000000000 : ℝ)*X 0 1+(803063321/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((6827901219/10000000000 : ℝ)*X 1 0+(713135221/2000000000 : ℝ)*X 1 1+(443931687/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((8898574679/10000000000 : ℝ)*X 2 0+(-1827670463/10000000000 : ℝ)*X 2 1+(-797183857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-5034679/1250000000 : ℝ)*X 0 0+(-1534153853/10000000000 : ℝ)*X 0 1+(1868896799/2000000000 : ℝ)*X 0 2+(-5034679/1250000000 : ℝ)*X 1 0+(-1534153853/10000000000 : ℝ)*X 1 1+(1868896799/2000000000 : ℝ)*X 1 2+(-5034679/1250000000 : ℝ)*X 2 0+(-1534153853/10000000000 : ℝ)*X 2 1+(1868896799/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-750966029/2000000000 : ℝ)*X 0 0+(-1153432289/2500000000 : ℝ)*X 0 1+(579774067/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2865231199/10000000000 : ℝ)*X 1 0+(6177863521/10000000000 : ℝ)*X 1 1+(235655711/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((121032421/156250000 : ℝ)*X 2 0+(-2823706269/10000000000 : ℝ)*X 2 1+(-52907839/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((14599/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14599/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4237276038168153647361/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69951773479/1000000000000 : ℝ)*(base1) + (180878900337/500000000000 : ℝ)*(base7) + (42559653889/250000000000 : ℝ)*(base43) + (127246846871/125000000000 : ℝ)*(base54) + (255165763533/500000000000 : ℝ)*(base60) + (1048306891399/500000000000 : ℝ)*(major_s0_0) + (963187583621/500000000000 : ℝ)*(major_s0_1) + (107863900783/100000000000 : ℝ)*(major_s0_2) + (148464037/1000000000000 : ℝ)*(sp_s0_6) + (2484104797239/1000000000000 : ℝ)*(sp_s0_7) + (2584404930091/1000000000000 : ℝ)*(sp_s0_8) + (1396191539567/1000000000000 : ℝ)*(sp_s0_9) + (164004223143/250000000000 : ℝ)*(sp_s0_13) + (6645387/500000000000 : ℝ)*(sp_s0_21) + (691167052191/500000000000 : ℝ)*(f.failure) + (2584404930091/1000000000000 : ℝ)*(f.sum) + (21594514248527/200000000000000000000000000 : ℝ)*base62 + (8997639320621/10000000000000000000000000 : ℝ)*base64 + (425487430159953/1000000000000000000000000000 : ℝ)*base67 + (84887451333581/200000000000000000000000000 : ℝ)*base69 + (1406625338807/1000000000000000000000000000 : ℝ)*base71 + (7492087221213/50000000000000000000000000 : ℝ)*base73 + (21451052654473/50000000000000000000000000 : ℝ)*base75 + (401886303499093/1000000000000000000000000000 : ℝ)*base76 + (229850981084213/1000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1669/6250000000000000 : ℝ)*base87 + (1669/6250000000000000 : ℝ)*base89 + (1669/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-11769/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-11769/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11358749498967738057453/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (243741402883/500000000000 : ℝ)*(base1) + (1078545996951/1000000000000 : ℝ)*(base7) + (7818507/500000000000 : ℝ)*(base21) + (2173331/1000000000000 : ℝ)*(base40) + (1079999/1000000000000 : ℝ)*(base53) + (349123/62500000000 : ℝ)*(base54) + (139334050003/500000000000 : ℝ)*(base60) + (48253333537/25000000000 : ℝ)*(major_s0_0) + (48253333537/25000000000 : ℝ)*(major_s0_1) + (1930126675513/1000000000000 : ℝ)*(major_s0_2) + (2399928689913/1000000000000 : ℝ)*(sp_s0_14) + (1912445884147/1000000000000 : ℝ)*(sp_s0_15) + (478106435291/250000000000 : ℝ)*(sp_s0_16) + (1863628245467/1000000000000 : ℝ)*(sp_s0_20) + (5090282561/4000000000 : ℝ)*(f.failure) + (956223482073/500000000000 : ℝ)*(f.sum) + (876036021227509/2000000000000000000000000000 : ℝ)*base62 + (12283128823869/100000000000000000000000000 : ℝ)*base65 + (19226186295659/50000000000000000000000000 : ℝ)*base66 + (250982357452309/2000000000000000000000000000 : ℝ)*base68 + (59374057672551/100000000000000000000000000 : ℝ)*base71 + (1787807726281/2500000000000000000000000 : ℝ)*base72 + (803778670781/2500000000000000000000000 : ℝ)*base75 + (3373573635659/50000000000000000000000000 : ℝ)*base76 + (9286497111279/50000000000000000000000000 : ℝ)*base78 + (1/50000000000000 : ℝ)*base86 + (1/50000000000000 : ℝ)*base88 + (1/50000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3533/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3533/6250 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (290120478319859235147/50000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2830103880657/1000000000000 : ℝ)*(base1) + (236645596501/250000000000 : ℝ)*(base7) + (354974646403/250000000000 : ℝ)*(base40) + (406453754683/1000000000000 : ℝ)*(base60) + (285677472137/100000000000 : ℝ)*(major_s0_0) + (285677472137/100000000000 : ℝ)*(major_s0_1) + (285677472137/100000000000 : ℝ)*(major_s0_2) + (25909113/1000000000000 : ℝ)*(sp_s0_1) + (1173183/250000000000 : ℝ)*(sp_s0_2) + (555851/100000000000 : ℝ)*(sp_s0_7) + (6336339/1000000000000 : ℝ)*(sp_s0_8) + (6067497501687/1000000000000 : ℝ)*(sp_s0_21) + (3237366934089/1000000000000 : ℝ)*(sp_s0_22) + (3237394486809/1000000000000 : ℝ)*(sp_s0_23) + (1883521494653/1000000000000 : ℝ)*(f.failure) + (3237399179541/1000000000000 : ℝ)*(f.sum) + (120609634347521/200000000000000000000000000 : ℝ)*base62 + (3017582362419/10000000000000000000000000 : ℝ)*base64 + (107959829919141/200000000000000000000000000 : ℝ)*base67 + (18128049599141/200000000000000000000000000 : ℝ)*base68 + (133106288090761/200000000000000000000000000 : ℝ)*base71 + (37978126581/10000000000000000000000000 : ℝ)*base72 + (2562312083581/10000000000000000000000000 : ℝ)*base75 + (26464751739141/200000000000000000000000000 : ℝ)*base77 + (52459515872479/200000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1227/12500000000000000 : ℝ)*base87 + (1227/12500000000000000 : ℝ)*base89 + (1227/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (14599/20000 : ℝ) ^ (33/8 : ℝ) ≤ (27295062351889210361/100000000000000000000 : ℝ) := by
    have hpowers : (14599/20000 : ℝ)^33 ≤ (27295062351889210361/100000000000000000000 : ℝ)^8 := by
      have hnat : (14599 : ℕ)^33*100000000000000000000^8 ≤ 27295062351889210361^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14599 20000 27295062351889210361 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14599/20000 : ℝ)) (X := (27295062351889210361/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (127295062351889210361/100000000000000000000 : ℝ) ≤ (1325314274366901/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (127295062351889210361/100000000000000000000 : ℝ)^8 ≤ (1325314274366901/1250000000000000 : ℝ)^33 := by
      have hnat : (127295062351889210361 : ℕ)^8*1250000000000000^33 ≤ 1325314274366901^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127295062351889210361 100000000000000000000 1325314274366901 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1325314274366901/1250000000000000 : ℝ)) (X := (127295062351889210361/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (77295062351889210361/50000000000000000000 : ℝ) ≤ (444551656792447/400000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (77295062351889210361/50000000000000000000 : ℝ)^8 ≤ (444551656792447/400000000000000 : ℝ)^33 := by
      have hnat : (77295062351889210361 : ℕ)^8*400000000000000^33 ≤ 444551656792447^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77295062351889210361 50000000000000000000 444551656792447 400000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (444551656792447/400000000000000 : ℝ)) (X := (77295062351889210361/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(75314274366901/912437500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(511277224875967/7299500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (14599/20000 : ℝ)) (alpha := (75314274366901/912437500000000 : ℝ)) (beta := (511277224875967/7299500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (14599/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(75314274366901/912437500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(511277224875967/7299500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (11769/12500 : ℝ) ^ (33/8 : ℝ) ≤ (38995715874564982493/50000000000000000000 : ℝ) := by
    have hpowers : (11769/12500 : ℝ)^33 ≤ (38995715874564982493/50000000000000000000 : ℝ)^8 := by
      have hnat : (11769 : ℕ)^33*50000000000000000000^8 ≤ 38995715874564982493^8*12500^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11769 12500 38995715874564982493 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11769/12500 : ℝ)) (X := (38995715874564982493/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (88995715874564982493/50000000000000000000 : ℝ) ≤ (11500131629354743/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (88995715874564982493/50000000000000000000 : ℝ)^8 ≤ (11500131629354743/10000000000000000 : ℝ)^33 := by
      have hnat : (88995715874564982493 : ℕ)^8*10000000000000000^33 ≤ 11500131629354743^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88995715874564982493 50000000000000000000 11500131629354743 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11500131629354743/10000000000000000 : ℝ)) (X := (88995715874564982493/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (63995715874564982493/25000000000000000000 : ℝ) ≤ (6279574551797593/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (63995715874564982493/25000000000000000000 : ℝ)^8 ≤ (6279574551797593/5000000000000000 : ℝ)^33 := by
      have hnat : (63995715874564982493 : ℕ)^8*5000000000000000^33 ≤ 6279574551797593^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63995715874564982493 25000000000000000000 6279574551797593 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6279574551797593/5000000000000000 : ℝ)) (X := (63995715874564982493/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(500043876451581/3138400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1059017474240443/9415200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (11769/12500 : ℝ)) (alpha := (500043876451581/3138400000000000 : ℝ)) (beta := (1059017474240443/9415200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (11769/12500 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(500043876451581/3138400000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1059017474240443/9415200000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (3533/6250 : ℝ) ^ (33/8 : ℝ) ≤ (9507961902314466459/100000000000000000000 : ℝ) := by
    have hpowers : (3533/6250 : ℝ)^33 ≤ (9507961902314466459/100000000000000000000 : ℝ)^8 := by
      have hnat : (3533 : ℕ)^33*100000000000000000000^8 ≤ 9507961902314466459^8*6250^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3533 6250 9507961902314466459 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3533/6250 : ℝ)) (X := (9507961902314466459/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (109507961902314466459/100000000000000000000 : ℝ) ≤ (5111314421954787/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (109507961902314466459/100000000000000000000 : ℝ)^8 ≤ (5111314421954787/5000000000000000 : ℝ)^33 := by
      have hnat : (109507961902314466459 : ℕ)^8*5000000000000000^33 ≤ 5111314421954787^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109507961902314466459 100000000000000000000 5111314421954787 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5111314421954787/5000000000000000 : ℝ)) (X := (109507961902314466459/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (59507961902314466459/50000000000000000000 : ℝ) ≤ (5215530706133421/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (59507961902314466459/50000000000000000000 : ℝ)^8 ≤ (5215530706133421/5000000000000000 : ℝ)^33 := by
      have hnat : (59507961902314466459 : ℕ)^8*5000000000000000^33 ≤ 5215530706133421^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59507961902314466459 50000000000000000000 5215530706133421 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5215530706133421/5000000000000000 : ℝ)) (X := (59507961902314466459/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(111314421954787/2826400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(52108142089317/1413200000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (3533/6250 : ℝ)) (alpha := (111314421954787/2826400000000000 : ℝ)) (beta := (52108142089317/1413200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (3533/6250 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(111314421954787/2826400000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(52108142089317/1413200000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3565172507/10000000000 : ℝ)*X 0 0+(-2082790693/5000000000 : ℝ)*X 0 1+(2621185823/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((269874999/625000000 : ℝ)*X 1 0+(2554354737/5000000000 : ℝ)*X 1 1+(3554539437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5875419267/10000000000 : ℝ)*X 2 0+(-2109408409/5000000000 : ℝ)*X 2 1+(-687302779/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((532955629/2500000000 : ℝ)*X 0 0+(-2646519551/10000000000 : ℝ)*X 0 1+(7591432977/10000000000 : ℝ)*X 0 2+(532955629/2500000000 : ℝ)*X 1 0+(-2646519551/10000000000 : ℝ)*X 1 1+(7591432977/10000000000 : ℝ)*X 1 2+(532955629/2500000000 : ℝ)*X 2 0+(-2646519551/10000000000 : ℝ)*X 2 1+(7591432977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304071_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-38127/6250 : ℝ) < ((-18959/12500 : ℝ)*P 0+(-18959/12500 : ℝ)*P 1+(-18959/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-38127/6250 : ℝ) < (-306957351317380968774489131098242089/50585385360250000000000000000000000 : ℝ) := by norm_num
    linear_combination (260266328329/1000000000000 : ℝ)*(base1) + (63023/100000000000 : ℝ)*(base15) + (209517/500000000000 : ℝ)*(base17) + (368273/1000000000000 : ℝ)*(base33) + (342414794063/1000000000000 : ℝ)*(base40) + (42493/1000000000000 : ℝ)*(base49) + (4147/10000000000 : ℝ)*(base59) + (425884947079/1000000000000 : ℝ)*(base60) + (1516719631727/1000000000000 : ℝ)*(major_s1_0) + (18959/12500 : ℝ)*(major_s1_1) + (18959/12500 : ℝ)*(major_s1_2) + (1141483738811/500000000000 : ℝ)*(sp_s1_0) + (505674932939/250000000000 : ℝ)*(sp_s1_1) + (101135039051/50000000000 : ℝ)*(sp_s1_2) + (739733671671/1000000000000 : ℝ)*(sp_s1_6) + (2022701149293/1000000000000 : ℝ)*(f.sum) + (108317990619918257/207899385000000000000000000000 : ℝ)*base62 + (22751193111329/35330000000000000000000000 : ℝ)*base65 + (7945527686817/39230000000000000000000000 : ℝ)*base66 + (710410344131/1766500000000000000000000 : ℝ)*base68 + (7915982301472949039/12894566750000000000000000000000 : ℝ)*base71 + (2113091174668041/7299500000000000000000000000 : ℝ)*base72 + (545974280023/919453125000000000000000 : ℝ)*base74 + (1327602444285083/3649750000000000000000000000 : ℝ)*base77 + (1714530859001630643/28635938500000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c304072_s0_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-434185021/1000000000 : ℝ)*x 0 + (-434185021/1000000000 : ℝ)*x 1 + (-434185021/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434185021/1000000000 : ℝ)^133 ≤ (16666666664599/50000000000000 : ℝ)^101 := by
    have hnat : (434185021 : ℕ)^133*50000000000000^101 ≤ 16666666664599^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434185021 1000000000 16666666664599 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434185021/1000000000 : ℝ)^133 ≤ (16666666664599/50000000000000 : ℝ)^101 := by
    have hnat : (434185021 : ℕ)^133*50000000000000^101 ≤ 16666666664599^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434185021 1000000000 16666666664599 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434185021/1000000000 : ℝ)^133 ≤ (16666666664599/50000000000000 : ℝ)^101 := by
    have hnat : (434185021 : ℕ)^133*50000000000000^101 ≤ 16666666664599^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434185021 1000000000 16666666664599 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-434185021/1000000000 : ℝ), (-434185021/1000000000 : ℝ), (-434185021/1000000000 : ℝ)] ![(16666666664599/50000000000000 : ℝ), (16666666664599/50000000000000 : ℝ), (16666666664599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-434185021/1000000000 : ℝ)|^133 ≤ (16666666664599/50000000000000 : ℝ)^101
        have hw : |(-434185021/1000000000 : ℝ)|=(434185021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-434185021/1000000000 : ℝ)|^133 ≤ (16666666664599/50000000000000 : ℝ)^101
        have hw : |(-434185021/1000000000 : ℝ)|=(434185021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434185021/1000000000 : ℝ)|^133 ≤ (16666666664599/50000000000000 : ℝ)^101
        have hw : |(-434185021/1000000000 : ℝ)|=(434185021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304072_s0_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (434185021/1000000000 : ℝ)*x 0 + (434185021/1000000000 : ℝ)*x 1 + (-434185021/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434185021/1000000000 : ℝ)^133 ≤ (16666666664599/50000000000000 : ℝ)^101 := by
    have hnat : (434185021 : ℕ)^133*50000000000000^101 ≤ 16666666664599^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434185021 1000000000 16666666664599 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434185021/1000000000 : ℝ)^133 ≤ (16666666664599/50000000000000 : ℝ)^101 := by
    have hnat : (434185021 : ℕ)^133*50000000000000^101 ≤ 16666666664599^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434185021 1000000000 16666666664599 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434185021/1000000000 : ℝ)^133 ≤ (16666666664599/50000000000000 : ℝ)^101 := by
    have hnat : (434185021 : ℕ)^133*50000000000000^101 ≤ 16666666664599^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434185021 1000000000 16666666664599 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434185021/1000000000 : ℝ), (434185021/1000000000 : ℝ), (-434185021/1000000000 : ℝ)] ![(16666666664599/50000000000000 : ℝ), (16666666664599/50000000000000 : ℝ), (16666666664599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434185021/1000000000 : ℝ)|^133 ≤ (16666666664599/50000000000000 : ℝ)^101
        have hw : |(434185021/1000000000 : ℝ)|=(434185021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(434185021/1000000000 : ℝ)|^133 ≤ (16666666664599/50000000000000 : ℝ)^101
        have hw : |(434185021/1000000000 : ℝ)|=(434185021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434185021/1000000000 : ℝ)|^133 ≤ (16666666664599/50000000000000 : ℝ)^101
        have hw : |(-434185021/1000000000 : ℝ)|=(434185021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304072_s0_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (434185021/1000000000 : ℝ)*x 0 + (-434185021/1000000000 : ℝ)*x 1 + (434185021/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434185021/1000000000 : ℝ)^133 ≤ (16666666664599/50000000000000 : ℝ)^101 := by
    have hnat : (434185021 : ℕ)^133*50000000000000^101 ≤ 16666666664599^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434185021 1000000000 16666666664599 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434185021/1000000000 : ℝ)^133 ≤ (16666666664599/50000000000000 : ℝ)^101 := by
    have hnat : (434185021 : ℕ)^133*50000000000000^101 ≤ 16666666664599^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434185021 1000000000 16666666664599 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434185021/1000000000 : ℝ)^133 ≤ (16666666664599/50000000000000 : ℝ)^101 := by
    have hnat : (434185021 : ℕ)^133*50000000000000^101 ≤ 16666666664599^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434185021 1000000000 16666666664599 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434185021/1000000000 : ℝ), (-434185021/1000000000 : ℝ), (434185021/1000000000 : ℝ)] ![(16666666664599/50000000000000 : ℝ), (16666666664599/50000000000000 : ℝ), (16666666664599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434185021/1000000000 : ℝ)|^133 ≤ (16666666664599/50000000000000 : ℝ)^101
        have hw : |(434185021/1000000000 : ℝ)|=(434185021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-434185021/1000000000 : ℝ)|^133 ≤ (16666666664599/50000000000000 : ℝ)^101
        have hw : |(-434185021/1000000000 : ℝ)|=(434185021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(434185021/1000000000 : ℝ)|^133 ≤ (16666666664599/50000000000000 : ℝ)^101
        have hw : |(434185021/1000000000 : ℝ)|=(434185021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304072_s0_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (434185021/1000000000 : ℝ)*x 0 + (-434185021/1000000000 : ℝ)*x 1 + (-434185021/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434185021/1000000000 : ℝ)^133 ≤ (16666666664599/50000000000000 : ℝ)^101 := by
    have hnat : (434185021 : ℕ)^133*50000000000000^101 ≤ 16666666664599^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434185021 1000000000 16666666664599 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434185021/1000000000 : ℝ)^133 ≤ (16666666664599/50000000000000 : ℝ)^101 := by
    have hnat : (434185021 : ℕ)^133*50000000000000^101 ≤ 16666666664599^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434185021 1000000000 16666666664599 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434185021/1000000000 : ℝ)^133 ≤ (16666666664599/50000000000000 : ℝ)^101 := by
    have hnat : (434185021 : ℕ)^133*50000000000000^101 ≤ 16666666664599^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434185021 1000000000 16666666664599 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434185021/1000000000 : ℝ), (-434185021/1000000000 : ℝ), (-434185021/1000000000 : ℝ)] ![(16666666664599/50000000000000 : ℝ), (16666666664599/50000000000000 : ℝ), (16666666664599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434185021/1000000000 : ℝ)|^133 ≤ (16666666664599/50000000000000 : ℝ)^101
        have hw : |(434185021/1000000000 : ℝ)|=(434185021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-434185021/1000000000 : ℝ)|^133 ≤ (16666666664599/50000000000000 : ℝ)^101
        have hw : |(-434185021/1000000000 : ℝ)|=(434185021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434185021/1000000000 : ℝ)|^133 ≤ (16666666664599/50000000000000 : ℝ)^101
        have hw : |(-434185021/1000000000 : ℝ)|=(434185021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304072 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base6 : ((-1 : ℝ)*T) ≤ (-1 : ℝ) := by
    linarith only [f.Tone]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (33/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^33 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^33*1^8 ≤ 1^8*1^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2365957637479293/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (2365957637479293/2000000000000000 : ℝ)^33 := by
      have hnat : (2 : ℕ)^8*2000000000000000^33 ≤ 2365957637479293^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2365957637479293 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2365957637479293/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (2610332041891033/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (2610332041891033/2000000000000000 : ℝ)^33 := by
      have hnat : (3 : ℕ)^8*2000000000000000^33 ≤ 2610332041891033^33*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 2610332041891033 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2610332041891033/2000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-434185021/1000000000 : ℝ)*X 0 0+(-434185021/1000000000 : ℝ)*X 0 1+(-434185021/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304072_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((434185021/1000000000 : ℝ)*X 1 0+(434185021/1000000000 : ℝ)*X 1 1+(-434185021/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304072_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((434185021/1000000000 : ℝ)*X 2 0+(-434185021/1000000000 : ℝ)*X 2 1+(434185021/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304072_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((434185021/1000000000 : ℝ)*X 0 0+(-434185021/1000000000 : ℝ)*X 0 1+(-434185021/1000000000 : ℝ)*X 0 2+(434185021/1000000000 : ℝ)*X 1 0+(-434185021/1000000000 : ℝ)*X 1 1+(-434185021/1000000000 : ℝ)*X 1 2+(434185021/1000000000 : ℝ)*X 2 0+(-434185021/1000000000 : ℝ)*X 2 1+(-434185021/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304072_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-38127/6250 : ℝ) < ((-18959/12500 : ℝ)*P 0+(-18959/12500 : ℝ)*P 1+(-18959/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-38127/6250 : ℝ) < (-2993257313454029080979/500000000000000000000 : ℝ) := by norm_num
    linear_combination (212159488427/1000000000000 : ℝ)*(base6) + (92203860629/1000000000000 : ℝ)*(base39) + (92203860629/1000000000000 : ℝ)*(base49) + (92203860629/1000000000000 : ℝ)*(base59) + (18959/12500 : ℝ)*(major_s0_0) + (18959/12500 : ℝ)*(major_s0_1) + (18959/12500 : ℝ)*(major_s0_2) + (2066224705111/1000000000000 : ℝ)*(sp_s0_0) + (2066224705111/1000000000000 : ℝ)*(sp_s0_1) + (2066224705111/1000000000000 : ℝ)*(sp_s0_2) + (787840511573/1000000000000 : ℝ)*(sp_s0_6) + (2066224705111/1000000000000 : ℝ)*(f.sum) + (59595791/500000000000000000000 : ℝ)*base62 + (190809/250000000000000000000 : ℝ)*base64 + (27182461/250000000000000000000 : ℝ)*base67 + (27182461/250000000000000000000 : ℝ)*base68 + (59595791/500000000000000000000 : ℝ)*base71 + (190809/250000000000000000000 : ℝ)*base72 + (190809/250000000000000000000 : ℝ)*base75 + (27182461/250000000000000000000 : ℝ)*base77 + (59595791/500000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p004_b032 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (c : Fin 88) (hlo : 71 ≤ c.val) (hhi : c.val < 73)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=71 ∨ c=72 := by omega
  rcases hc with rfl|rfl
  · exact collision_c304071 p hpa (by linarith only [hpb]) X hX
  · exact collision_c304072 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (c : Fin 88) (hlo : 71 ≤ c.val) (hhi : c.val < 73)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p004_b032 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

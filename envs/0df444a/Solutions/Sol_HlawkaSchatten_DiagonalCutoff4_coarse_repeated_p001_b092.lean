-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b092
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:32:39.915419+00:00
-- url     : https://prove2.me/submissions/4fd02b1c-3070-4ea3-81c8-9ed27454e3ae

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
theorem collision_support_c201245_s0_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-76007/10000000000 : ℝ)*x 0 + (9633742711/10000000000 : ℝ)*x 1 + (-487401901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76007/10000000000 : ℝ)^17 ≤ (4043539/20000000000000 : ℝ)^13 := by
    have hnat : (76007 : ℕ)^17*20000000000000^13 ≤ 4043539^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76007 10000000000 4043539 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9633742711/10000000000 : ℝ)^17 ≤ (47618850472149/50000000000000 : ℝ)^13 := by
    have hnat : (9633742711 : ℕ)^17*50000000000000^13 ≤ 47618850472149^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9633742711 10000000000 47618850472149 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (487401901/5000000000 : ℝ)^17 ≤ (59528485263/1250000000000 : ℝ)^13 := by
    have hnat : (487401901 : ℕ)^17*1250000000000^13 ≤ 59528485263^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487401901 5000000000 59528485263 1250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-76007/10000000000 : ℝ), (9633742711/10000000000 : ℝ), (-487401901/5000000000 : ℝ)] ![(4043539/20000000000000 : ℝ), (47618850472149/50000000000000 : ℝ), (59528485263/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-76007/10000000000 : ℝ)|^17 ≤ (4043539/20000000000000 : ℝ)^13
        have hw : |(-76007/10000000000 : ℝ)|=(76007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9633742711/10000000000 : ℝ)|^17 ≤ (47618850472149/50000000000000 : ℝ)^13
        have hw : |(9633742711/10000000000 : ℝ)|=(9633742711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-487401901/5000000000 : ℝ)|^17 ≤ (59528485263/1250000000000 : ℝ)^13
        have hw : |(-487401901/5000000000 : ℝ)|=(487401901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s0_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (9120703111/10000000000 : ℝ)*x 0 + (903129/2000000000 : ℝ)*x 1 + (94600571/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9120703111/10000000000 : ℝ)^17 ≤ (22165082348837/25000000000000 : ℝ)^13 := by
    have hnat : (9120703111 : ℕ)^17*25000000000000^13 ≤ 22165082348837^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9120703111 10000000000 22165082348837 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903129/2000000000 : ℝ)^17 ≤ (4220878057/100000000000000 : ℝ)^13 := by
    have hnat : (903129 : ℕ)^17*100000000000000^13 ≤ 4220878057^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903129 2000000000 4220878057 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94600571/500000000 : ℝ)^17 ≤ (11335449709231/100000000000000 : ℝ)^13 := by
    have hnat : (94600571 : ℕ)^17*100000000000000^13 ≤ 11335449709231^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94600571 500000000 11335449709231 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9120703111/10000000000 : ℝ), (903129/2000000000 : ℝ), (94600571/500000000 : ℝ)] ![(22165082348837/25000000000000 : ℝ), (4220878057/100000000000000 : ℝ), (11335449709231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9120703111/10000000000 : ℝ)|^17 ≤ (22165082348837/25000000000000 : ℝ)^13
        have hw : |(9120703111/10000000000 : ℝ)|=(9120703111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903129/2000000000 : ℝ)|^17 ≤ (4220878057/100000000000000 : ℝ)^13
        have hw : |(903129/2000000000 : ℝ)|=(903129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(94600571/500000000 : ℝ)|^17 ≤ (11335449709231/100000000000000 : ℝ)^13
        have hw : |(94600571/500000000 : ℝ)|=(94600571/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s0_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4178047099/5000000000 : ℝ)*x 0 + (2614437763/10000000000 : ℝ)*x 1 + (791848199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4178047099/5000000000 : ℝ)^17 ≤ (79068654922749/100000000000000 : ℝ)^13 := by
    have hnat : (4178047099 : ℕ)^17*100000000000000^13 ≤ 79068654922749^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4178047099 5000000000 79068654922749 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614437763/10000000000 : ℝ)^17 ≤ (4325637320461/25000000000000 : ℝ)^13 := by
    have hnat : (2614437763 : ℕ)^17*25000000000000^13 ≤ 4325637320461^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614437763 10000000000 4325637320461 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (791848199/10000000000 : ℝ)^17 ≤ (1814397891327/50000000000000 : ℝ)^13 := by
    have hnat : (791848199 : ℕ)^17*50000000000000^13 ≤ 1814397891327^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791848199 10000000000 1814397891327 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4178047099/5000000000 : ℝ), (2614437763/10000000000 : ℝ), (791848199/10000000000 : ℝ)] ![(79068654922749/100000000000000 : ℝ), (4325637320461/25000000000000 : ℝ), (1814397891327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4178047099/5000000000 : ℝ)|^17 ≤ (79068654922749/100000000000000 : ℝ)^13
        have hw : |(4178047099/5000000000 : ℝ)|=(4178047099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614437763/10000000000 : ℝ)|^17 ≤ (4325637320461/25000000000000 : ℝ)^13
        have hw : |(2614437763/10000000000 : ℝ)|=(2614437763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(791848199/10000000000 : ℝ)|^17 ≤ (1814397891327/50000000000000 : ℝ)^13
        have hw : |(791848199/10000000000 : ℝ)|=(791848199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s0_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-109106667/5000000000 : ℝ)*x 0 + (3145944653/10000000000 : ℝ)*x 1 + (8211749519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109106667/5000000000 : ℝ)^17 ≤ (84077123893/12500000000000 : ℝ)^13 := by
    have hnat : (109106667 : ℕ)^17*12500000000000^13 ≤ 84077123893^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109106667 5000000000 84077123893 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3145944653/10000000000 : ℝ)^17 ≤ (11020034449889/50000000000000 : ℝ)^13 := by
    have hnat : (3145944653 : ℕ)^17*50000000000000^13 ≤ 11020034449889^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3145944653 10000000000 11020034449889 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8211749519/10000000000 : ℝ)^17 ≤ (15457462818989/20000000000000 : ℝ)^13 := by
    have hnat : (8211749519 : ℕ)^17*20000000000000^13 ≤ 15457462818989^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8211749519 10000000000 15457462818989 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109106667/5000000000 : ℝ), (3145944653/10000000000 : ℝ), (8211749519/10000000000 : ℝ)] ![(84077123893/12500000000000 : ℝ), (11020034449889/50000000000000 : ℝ), (15457462818989/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109106667/5000000000 : ℝ)|^17 ≤ (84077123893/12500000000000 : ℝ)^13
        have hw : |(-109106667/5000000000 : ℝ)|=(109106667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3145944653/10000000000 : ℝ)|^17 ≤ (11020034449889/50000000000000 : ℝ)^13
        have hw : |(3145944653/10000000000 : ℝ)|=(3145944653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8211749519/10000000000 : ℝ)|^17 ≤ (15457462818989/20000000000000 : ℝ)^13
        have hw : |(8211749519/10000000000 : ℝ)|=(8211749519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s0_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2801591/10000000000 : ℝ)*x 0 + (9576776977/10000000000 : ℝ)*x 1 + (-543831347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2801591/10000000000 : ℝ)^17 ≤ (565247313/25000000000000 : ℝ)^13 := by
    have hnat : (2801591 : ℕ)^17*25000000000000^13 ≤ 565247313^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2801591 10000000000 565247313 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9576776977/10000000000 : ℝ)^17 ≤ (94501938999787/100000000000000 : ℝ)^13 := by
    have hnat : (9576776977 : ℕ)^17*100000000000000^13 ≤ 94501938999787^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9576776977 10000000000 94501938999787 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543831347/5000000000 : ℝ)^17 ≤ (219832000049/4000000000000 : ℝ)^13 := by
    have hnat : (543831347 : ℕ)^17*4000000000000^13 ≤ 219832000049^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543831347 5000000000 219832000049 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2801591/10000000000 : ℝ), (9576776977/10000000000 : ℝ), (-543831347/5000000000 : ℝ)] ![(565247313/25000000000000 : ℝ), (94501938999787/100000000000000 : ℝ), (219832000049/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2801591/10000000000 : ℝ)|^17 ≤ (565247313/25000000000000 : ℝ)^13
        have hw : |(-2801591/10000000000 : ℝ)|=(2801591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9576776977/10000000000 : ℝ)|^17 ≤ (94501938999787/100000000000000 : ℝ)^13
        have hw : |(9576776977/10000000000 : ℝ)|=(9576776977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-543831347/5000000000 : ℝ)|^17 ≤ (219832000049/4000000000000 : ℝ)^13
        have hw : |(-543831347/5000000000 : ℝ)|=(543831347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s0_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1814402003/2000000000 : ℝ)*x 0 + (62736923/10000000000 : ℝ)*x 1 + (977178311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1814402003/2000000000 : ℝ)^17 ≤ (88041862175513/100000000000000 : ℝ)^13 := by
    have hnat : (1814402003 : ℕ)^17*100000000000000^13 ≤ 88041862175513^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814402003 2000000000 88041862175513 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62736923/10000000000 : ℝ)^17 ≤ (131776524641/100000000000000 : ℝ)^13 := by
    have hnat : (62736923 : ℕ)^17*100000000000000^13 ≤ 131776524641^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62736923 10000000000 131776524641 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (977178311/5000000000 : ℝ)^17 ≤ (11826361287199/100000000000000 : ℝ)^13 := by
    have hnat : (977178311 : ℕ)^17*100000000000000^13 ≤ 11826361287199^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977178311 5000000000 11826361287199 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1814402003/2000000000 : ℝ), (62736923/10000000000 : ℝ), (977178311/5000000000 : ℝ)] ![(88041862175513/100000000000000 : ℝ), (131776524641/100000000000000 : ℝ), (11826361287199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1814402003/2000000000 : ℝ)|^17 ≤ (88041862175513/100000000000000 : ℝ)^13
        have hw : |(1814402003/2000000000 : ℝ)|=(1814402003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(62736923/10000000000 : ℝ)|^17 ≤ (131776524641/100000000000000 : ℝ)^13
        have hw : |(62736923/10000000000 : ℝ)|=(62736923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(977178311/5000000000 : ℝ)|^17 ≤ (11826361287199/100000000000000 : ℝ)^13
        have hw : |(977178311/5000000000 : ℝ)|=(977178311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s0_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3539067733/5000000000 : ℝ)*x 0 + (4281979583/10000000000 : ℝ)*x 1 + (374523897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3539067733/5000000000 : ℝ)^17 ≤ (31820724634839/50000000000000 : ℝ)^13 := by
    have hnat : (3539067733 : ℕ)^17*50000000000000^13 ≤ 31820724634839^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3539067733 5000000000 31820724634839 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4281979583/10000000000 : ℝ)^17 ≤ (32984086955219/100000000000000 : ℝ)^13 := by
    have hnat : (4281979583 : ℕ)^17*100000000000000^13 ≤ 32984086955219^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4281979583 10000000000 32984086955219 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (374523897/5000000000 : ℝ)^17 ≤ (674892753111/20000000000000 : ℝ)^13 := by
    have hnat : (374523897 : ℕ)^17*20000000000000^13 ≤ 674892753111^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374523897 5000000000 674892753111 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3539067733/5000000000 : ℝ), (4281979583/10000000000 : ℝ), (374523897/5000000000 : ℝ)] ![(31820724634839/50000000000000 : ℝ), (32984086955219/100000000000000 : ℝ), (674892753111/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3539067733/5000000000 : ℝ)|^17 ≤ (31820724634839/50000000000000 : ℝ)^13
        have hw : |(3539067733/5000000000 : ℝ)|=(3539067733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4281979583/10000000000 : ℝ)|^17 ≤ (32984086955219/100000000000000 : ℝ)^13
        have hw : |(4281979583/10000000000 : ℝ)|=(4281979583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(374523897/5000000000 : ℝ)|^17 ≤ (674892753111/20000000000000 : ℝ)^13
        have hw : |(374523897/5000000000 : ℝ)|=(374523897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s0_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1117154237/5000000000 : ℝ)*x 0 + (8185656777/10000000000 : ℝ)*x 1 + (789270647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1117154237/5000000000 : ℝ)^17 ≤ (14088977681883/100000000000000 : ℝ)^13 := by
    have hnat : (1117154237 : ℕ)^17*100000000000000^13 ≤ 14088977681883^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117154237 5000000000 14088977681883 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8185656777/10000000000 : ℝ)^17 ≤ (38483164339719/50000000000000 : ℝ)^13 := by
    have hnat : (8185656777 : ℕ)^17*50000000000000^13 ≤ 38483164339719^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8185656777 10000000000 38483164339719 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (789270647/5000000000 : ℝ)^17 ≤ (8944693624307/100000000000000 : ℝ)^13 := by
    have hnat : (789270647 : ℕ)^17*100000000000000^13 ≤ 8944693624307^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789270647 5000000000 8944693624307 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1117154237/5000000000 : ℝ), (8185656777/10000000000 : ℝ), (789270647/5000000000 : ℝ)] ![(14088977681883/100000000000000 : ℝ), (38483164339719/50000000000000 : ℝ), (8944693624307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1117154237/5000000000 : ℝ)|^17 ≤ (14088977681883/100000000000000 : ℝ)^13
        have hw : |(-1117154237/5000000000 : ℝ)|=(1117154237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8185656777/10000000000 : ℝ)|^17 ≤ (38483164339719/50000000000000 : ℝ)^13
        have hw : |(8185656777/10000000000 : ℝ)|=(8185656777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(789270647/5000000000 : ℝ)|^17 ≤ (8944693624307/100000000000000 : ℝ)^13
        have hw : |(789270647/5000000000 : ℝ)|=(789270647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s0_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (156710853/10000000000 : ℝ)*x 0 + (8700194729/10000000000 : ℝ)*x 1 + (-310911381/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156710853/10000000000 : ℝ)^17 ≤ (54532443321/12500000000000 : ℝ)^13 := by
    have hnat : (156710853 : ℕ)^17*12500000000000^13 ≤ 54532443321^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156710853 10000000000 54532443321 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8700194729/10000000000 : ℝ)^17 ≤ (20838310841853/25000000000000 : ℝ)^13 := by
    have hnat : (8700194729 : ℕ)^17*25000000000000^13 ≤ 20838310841853^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8700194729 10000000000 20838310841853 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310911381/1250000000 : ℝ)^17 ≤ (16210497067869/100000000000000 : ℝ)^13 := by
    have hnat : (310911381 : ℕ)^17*100000000000000^13 ≤ 16210497067869^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310911381 1250000000 16210497067869 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(156710853/10000000000 : ℝ), (8700194729/10000000000 : ℝ), (-310911381/1250000000 : ℝ)] ![(54532443321/12500000000000 : ℝ), (20838310841853/25000000000000 : ℝ), (16210497067869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(156710853/10000000000 : ℝ)|^17 ≤ (54532443321/12500000000000 : ℝ)^13
        have hw : |(156710853/10000000000 : ℝ)|=(156710853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8700194729/10000000000 : ℝ)|^17 ≤ (20838310841853/25000000000000 : ℝ)^13
        have hw : |(8700194729/10000000000 : ℝ)|=(8700194729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-310911381/1250000000 : ℝ)|^17 ≤ (16210497067869/100000000000000 : ℝ)^13
        have hw : |(-310911381/1250000000 : ℝ)|=(310911381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s0_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2105198863/2500000000 : ℝ)*x 0 + (5665663/10000000000 : ℝ)*x 1 + (2934593897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105198863/2500000000 : ℝ)^17 ≤ (39935106880973/50000000000000 : ℝ)^13 := by
    have hnat : (2105198863 : ℕ)^17*50000000000000^13 ≤ 39935106880973^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105198863 2500000000 39935106880973 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5665663/10000000000 : ℝ)^17 ≤ (2839363337/50000000000000 : ℝ)^13 := by
    have hnat : (5665663 : ℕ)^17*50000000000000^13 ≤ 2839363337^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5665663 10000000000 2839363337 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2934593897/10000000000 : ℝ)^17 ≤ (20124107494631/100000000000000 : ℝ)^13 := by
    have hnat : (2934593897 : ℕ)^17*100000000000000^13 ≤ 20124107494631^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934593897 10000000000 20124107494631 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2105198863/2500000000 : ℝ), (5665663/10000000000 : ℝ), (2934593897/10000000000 : ℝ)] ![(39935106880973/50000000000000 : ℝ), (2839363337/50000000000000 : ℝ), (20124107494631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2105198863/2500000000 : ℝ)|^17 ≤ (39935106880973/50000000000000 : ℝ)^13
        have hw : |(2105198863/2500000000 : ℝ)|=(2105198863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5665663/10000000000 : ℝ)|^17 ≤ (2839363337/50000000000000 : ℝ)^13
        have hw : |(5665663/10000000000 : ℝ)|=(5665663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2934593897/10000000000 : ℝ)|^17 ≤ (20124107494631/100000000000000 : ℝ)^13
        have hw : |(2934593897/10000000000 : ℝ)|=(2934593897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s0_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3997750911/5000000000 : ℝ)*x 0 + (2706563109/10000000000 : ℝ)*x 1 + (1345600839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3997750911/5000000000 : ℝ)^17 ≤ (74636644111547/100000000000000 : ℝ)^13 := by
    have hnat : (3997750911 : ℕ)^17*100000000000000^13 ≤ 74636644111547^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3997750911 5000000000 74636644111547 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706563109/10000000000 : ℝ)^17 ≤ (9052063577309/50000000000000 : ℝ)^13 := by
    have hnat : (2706563109 : ℕ)^17*50000000000000^13 ≤ 9052063577309^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706563109 10000000000 9052063577309 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1345600839/10000000000 : ℝ)^17 ≤ (72592287139/1000000000000 : ℝ)^13 := by
    have hnat : (1345600839 : ℕ)^17*1000000000000^13 ≤ 72592287139^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345600839 10000000000 72592287139 1000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3997750911/5000000000 : ℝ), (2706563109/10000000000 : ℝ), (1345600839/10000000000 : ℝ)] ![(74636644111547/100000000000000 : ℝ), (9052063577309/50000000000000 : ℝ), (72592287139/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3997750911/5000000000 : ℝ)|^17 ≤ (74636644111547/100000000000000 : ℝ)^13
        have hw : |(3997750911/5000000000 : ℝ)|=(3997750911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706563109/10000000000 : ℝ)|^17 ≤ (9052063577309/50000000000000 : ℝ)^13
        have hw : |(2706563109/10000000000 : ℝ)|=(2706563109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1345600839/10000000000 : ℝ)|^17 ≤ (72592287139/1000000000000 : ℝ)^13
        have hw : |(1345600839/10000000000 : ℝ)|=(1345600839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s0_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-4779103/2000000000 : ℝ)*x 0 + (474474037/500000000 : ℝ)*x 1 + (1249038933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4779103/2000000000 : ℝ)^17 ≤ (18647238297/50000000000000 : ℝ)^13 := by
    have hnat : (4779103 : ℕ)^17*50000000000000^13 ≤ 18647238297^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4779103 2000000000 18647238297 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474474037/500000000 : ℝ)^17 ≤ (46688522395389/50000000000000 : ℝ)^13 := by
    have hnat : (474474037 : ℕ)^17*50000000000000^13 ≤ 46688522395389^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474474037 500000000 46688522395389 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1249038933/10000000000 : ℝ)^17 ≤ (6585660718007/100000000000000 : ℝ)^13 := by
    have hnat : (1249038933 : ℕ)^17*100000000000000^13 ≤ 6585660718007^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249038933 10000000000 6585660718007 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4779103/2000000000 : ℝ), (474474037/500000000 : ℝ), (1249038933/10000000000 : ℝ)] ![(18647238297/50000000000000 : ℝ), (46688522395389/50000000000000 : ℝ), (6585660718007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4779103/2000000000 : ℝ)|^17 ≤ (18647238297/50000000000000 : ℝ)^13
        have hw : |(-4779103/2000000000 : ℝ)|=(4779103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(474474037/500000000 : ℝ)|^17 ≤ (46688522395389/50000000000000 : ℝ)^13
        have hw : |(474474037/500000000 : ℝ)|=(474474037/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1249038933/10000000000 : ℝ)|^17 ≤ (6585660718007/100000000000000 : ℝ)^13
        have hw : |(1249038933/10000000000 : ℝ)|=(1249038933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s0_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8889/5000000000 : ℝ)*x 0 + (1589025571/2500000000 : ℝ)*x 1 + (-5403486433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8889/5000000000 : ℝ)^17 ≤ (3024239/100000000000000 : ℝ)^13 := by
    have hnat : (8889 : ℕ)^17*100000000000000^13 ≤ 3024239^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8889 5000000000 3024239 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1589025571/2500000000 : ℝ)^17 ≤ (1382210643687/2500000000000 : ℝ)^13 := by
    have hnat : (1589025571 : ℕ)^17*2500000000000^13 ≤ 1382210643687^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1589025571 2500000000 1382210643687 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403486433/10000000000 : ℝ)^17 ≤ (22355785603539/50000000000000 : ℝ)^13 := by
    have hnat : (5403486433 : ℕ)^17*50000000000000^13 ≤ 22355785603539^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403486433 10000000000 22355785603539 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8889/5000000000 : ℝ), (1589025571/2500000000 : ℝ), (-5403486433/10000000000 : ℝ)] ![(3024239/100000000000000 : ℝ), (1382210643687/2500000000000 : ℝ), (22355785603539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8889/5000000000 : ℝ)|^17 ≤ (3024239/100000000000000 : ℝ)^13
        have hw : |(8889/5000000000 : ℝ)|=(8889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1589025571/2500000000 : ℝ)|^17 ≤ (1382210643687/2500000000000 : ℝ)^13
        have hw : |(1589025571/2500000000 : ℝ)|=(1589025571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5403486433/10000000000 : ℝ)|^17 ≤ (22355785603539/50000000000000 : ℝ)^13
        have hw : |(-5403486433/10000000000 : ℝ)|=(5403486433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s0_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8777399199/10000000000 : ℝ)*x 0 + (15273933/10000000000 : ℝ)*x 1 + (242213087/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8777399199/10000000000 : ℝ)^17 ≤ (42160908717273/50000000000000 : ℝ)^13 := by
    have hnat : (8777399199 : ℕ)^17*50000000000000^13 ≤ 42160908717273^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8777399199 10000000000 42160908717273 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15273933/10000000000 : ℝ)^17 ≤ (5192951159/25000000000000 : ℝ)^13 := by
    have hnat : (15273933 : ℕ)^17*25000000000000^13 ≤ 5192951159^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15273933 10000000000 5192951159 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (242213087/1000000000 : ℝ)^17 ≤ (1957176343233/12500000000000 : ℝ)^13 := by
    have hnat : (242213087 : ℕ)^17*12500000000000^13 ≤ 1957176343233^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242213087 1000000000 1957176343233 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8777399199/10000000000 : ℝ), (15273933/10000000000 : ℝ), (242213087/1000000000 : ℝ)] ![(42160908717273/50000000000000 : ℝ), (5192951159/25000000000000 : ℝ), (1957176343233/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8777399199/10000000000 : ℝ)|^17 ≤ (42160908717273/50000000000000 : ℝ)^13
        have hw : |(8777399199/10000000000 : ℝ)|=(8777399199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15273933/10000000000 : ℝ)|^17 ≤ (5192951159/25000000000000 : ℝ)^13
        have hw : |(15273933/10000000000 : ℝ)|=(15273933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(242213087/1000000000 : ℝ)|^17 ≤ (1957176343233/12500000000000 : ℝ)^13
        have hw : |(242213087/1000000000 : ℝ)|=(242213087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s0_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8558125163/10000000000 : ℝ)*x 0 + (1341758401/5000000000 : ℝ)*x 1 + (35813809/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8558125163/10000000000 : ℝ)^17 ≤ (81577813245681/100000000000000 : ℝ)^13 := by
    have hnat : (8558125163 : ℕ)^17*100000000000000^13 ≤ 81577813245681^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8558125163 10000000000 81577813245681 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1341758401/5000000000 : ℝ)^17 ≤ (8951401490557/50000000000000 : ℝ)^13 := by
    have hnat : (1341758401 : ℕ)^17*50000000000000^13 ≤ 8951401490557^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341758401 5000000000 8951401490557 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35813809/2000000000 : ℝ)^17 ≤ (103876752701/20000000000000 : ℝ)^13 := by
    have hnat : (35813809 : ℕ)^17*20000000000000^13 ≤ 103876752701^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35813809 2000000000 103876752701 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8558125163/10000000000 : ℝ), (1341758401/5000000000 : ℝ), (35813809/2000000000 : ℝ)] ![(81577813245681/100000000000000 : ℝ), (8951401490557/50000000000000 : ℝ), (103876752701/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8558125163/10000000000 : ℝ)|^17 ≤ (81577813245681/100000000000000 : ℝ)^13
        have hw : |(8558125163/10000000000 : ℝ)|=(8558125163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1341758401/5000000000 : ℝ)|^17 ≤ (8951401490557/50000000000000 : ℝ)^13
        have hw : |(1341758401/5000000000 : ℝ)|=(1341758401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35813809/2000000000 : ℝ)|^17 ≤ (103876752701/20000000000000 : ℝ)^13
        have hw : |(35813809/2000000000 : ℝ)|=(35813809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s1_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-59553/2500000000 : ℝ)*x 0 + (491367087/500000000 : ℝ)*x 1 + (34358891/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59553/2500000000 : ℝ)^17 ≤ (90051491/100000000000000 : ℝ)^13 := by
    have hnat : (59553 : ℕ)^17*100000000000000^13 ≤ 90051491^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59553 2500000000 90051491 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (491367087/500000000 : ℝ)^17 ≤ (48874091371029/50000000000000 : ℝ)^13 := by
    have hnat : (491367087 : ℕ)^17*50000000000000^13 ≤ 48874091371029^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491367087 500000000 48874091371029 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34358891/625000000 : ℝ)^17 ≤ (2251727193741/100000000000000 : ℝ)^13 := by
    have hnat : (34358891 : ℕ)^17*100000000000000^13 ≤ 2251727193741^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34358891 625000000 2251727193741 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-59553/2500000000 : ℝ), (491367087/500000000 : ℝ), (34358891/625000000 : ℝ)] ![(90051491/100000000000000 : ℝ), (48874091371029/50000000000000 : ℝ), (2251727193741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-59553/2500000000 : ℝ)|^17 ≤ (90051491/100000000000000 : ℝ)^13
        have hw : |(-59553/2500000000 : ℝ)|=(59553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(491367087/500000000 : ℝ)|^17 ≤ (48874091371029/50000000000000 : ℝ)^13
        have hw : |(491367087/500000000 : ℝ)|=(491367087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34358891/625000000 : ℝ)|^17 ≤ (2251727193741/100000000000000 : ℝ)^13
        have hw : |(34358891/625000000 : ℝ)|=(34358891/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s1_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-238287/10000000000 : ℝ)*x 0 + (191060807/200000000 : ℝ)*x 1 + (-567014087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (238287/10000000000 : ℝ)^17 ≤ (90088569/100000000000000 : ℝ)^13 := by
    have hnat : (238287 : ℕ)^17*100000000000000^13 ≤ 90088569^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238287 10000000000 90088569 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191060807/200000000 : ℝ)^17 ≤ (94195756623159/100000000000000 : ℝ)^13 := by
    have hnat : (191060807 : ℕ)^17*100000000000000^13 ≤ 94195756623159^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191060807 200000000 94195756623159 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567014087/5000000000 : ℝ)^17 ≤ (1451038321211/25000000000000 : ℝ)^13 := by
    have hnat : (567014087 : ℕ)^17*25000000000000^13 ≤ 1451038321211^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567014087 5000000000 1451038321211 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-238287/10000000000 : ℝ), (191060807/200000000 : ℝ), (-567014087/5000000000 : ℝ)] ![(90088569/100000000000000 : ℝ), (94195756623159/100000000000000 : ℝ), (1451038321211/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-238287/10000000000 : ℝ)|^17 ≤ (90088569/100000000000000 : ℝ)^13
        have hw : |(-238287/10000000000 : ℝ)|=(238287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(191060807/200000000 : ℝ)|^17 ≤ (94195756623159/100000000000000 : ℝ)^13
        have hw : |(191060807/200000000 : ℝ)|=(191060807/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-567014087/5000000000 : ℝ)|^17 ≤ (1451038321211/25000000000000 : ℝ)^13
        have hw : |(-567014087/5000000000 : ℝ)|=(567014087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s1_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4725364191/5000000000 : ℝ)*x 0 + (9461/5000000000 : ℝ)*x 1 + (132600477/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4725364191/5000000000 : ℝ)^17 ≤ (23219675498851/25000000000000 : ℝ)^13 := by
    have hnat : (4725364191 : ℕ)^17*25000000000000^13 ≤ 23219675498851^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4725364191 5000000000 23219675498851 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9461/5000000000 : ℝ)^17 ≤ (3281209/100000000000000 : ℝ)^13 := by
    have hnat : (9461 : ℕ)^17*100000000000000^13 ≤ 3281209^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9461 5000000000 3281209 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132600477/1000000000 : ℝ)^17 ≤ (890161838631/12500000000000 : ℝ)^13 := by
    have hnat : (132600477 : ℕ)^17*12500000000000^13 ≤ 890161838631^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132600477 1000000000 890161838631 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4725364191/5000000000 : ℝ), (9461/5000000000 : ℝ), (132600477/1000000000 : ℝ)] ![(23219675498851/25000000000000 : ℝ), (3281209/100000000000000 : ℝ), (890161838631/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4725364191/5000000000 : ℝ)|^17 ≤ (23219675498851/25000000000000 : ℝ)^13
        have hw : |(4725364191/5000000000 : ℝ)|=(4725364191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9461/5000000000 : ℝ)|^17 ≤ (3281209/100000000000000 : ℝ)^13
        have hw : |(9461/5000000000 : ℝ)|=(9461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132600477/1000000000 : ℝ)|^17 ≤ (890161838631/12500000000000 : ℝ)^13
        have hw : |(132600477/1000000000 : ℝ)|=(132600477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201245_s1_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2190774793/2500000000 : ℝ)*x 0 + (198913469/1000000000 : ℝ)*x 1 + (20322493/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190774793/2500000000 : ℝ)^17 ≤ (42071108449689/50000000000000 : ℝ)^13 := by
    have hnat : (2190774793 : ℕ)^17*50000000000000^13 ≤ 42071108449689^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190774793 2500000000 42071108449689 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198913469/1000000000 : ℝ)^17 ≤ (6051158969199/50000000000000 : ℝ)^13 := by
    have hnat : (198913469 : ℕ)^17*50000000000000^13 ≤ 6051158969199^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198913469 1000000000 6051158969199 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20322493/250000000 : ℝ)^17 ≤ (3755465141493/100000000000000 : ℝ)^13 := by
    have hnat : (20322493 : ℕ)^17*100000000000000^13 ≤ 3755465141493^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20322493 250000000 3755465141493 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2190774793/2500000000 : ℝ), (198913469/1000000000 : ℝ), (20322493/250000000 : ℝ)] ![(42071108449689/50000000000000 : ℝ), (6051158969199/50000000000000 : ℝ), (3755465141493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2190774793/2500000000 : ℝ)|^17 ≤ (42071108449689/50000000000000 : ℝ)^13
        have hw : |(2190774793/2500000000 : ℝ)|=(2190774793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(198913469/1000000000 : ℝ)|^17 ≤ (6051158969199/50000000000000 : ℝ)^13
        have hw : |(198913469/1000000000 : ℝ)|=(198913469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20322493/250000000 : ℝ)|^17 ≤ (3755465141493/100000000000000 : ℝ)^13
        have hw : |(20322493/250000000 : ℝ)|=(20322493/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c201245 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![0, 2, 1], ![1, 2, 0]] ![![true, true, true], ![true, true, true], ![false, true, false]]) : False := by
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
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) ∧ ((1 : ℝ)*(X 0 1+X 2 1)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 1) ∧ ((1 : ℝ)*pair X 1 1) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) ∧ ((-1 : ℝ)*(X 0 2+X 1 2)) ≤ ((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) ∧ ((-1 : ℝ)*pair X 2 2) ≤ ((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
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
      X ![![0, 1, 2], ![0, 2, 1], ![1, 2, 0]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 0+X 2 0))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![0, 2, 1], ![1, 2, 0]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 0)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 1 1) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 1+X 1 1))+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 1 2))+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![0, 2, 1], ![1, 2, 0]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 1)+(365957637479293/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 2)+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((-76007/10000000000 : ℝ)*X 1 0+(9633742711/10000000000 : ℝ)*X 1 1+(-487401901/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((9120703111/10000000000 : ℝ)*X 2 0+(903129/2000000000 : ℝ)*X 2 1+(94600571/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((4178047099/5000000000 : ℝ)*X 0 0+(2614437763/10000000000 : ℝ)*X 0 1+(791848199/10000000000 : ℝ)*X 0 2+(4178047099/5000000000 : ℝ)*X 1 0+(2614437763/10000000000 : ℝ)*X 1 1+(791848199/10000000000 : ℝ)*X 1 2+(4178047099/5000000000 : ℝ)*X 2 0+(2614437763/10000000000 : ℝ)*X 2 1+(791848199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-109106667/5000000000 : ℝ)*X 0 0+(3145944653/10000000000 : ℝ)*X 0 1+(8211749519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((-2801591/10000000000 : ℝ)*X 1 0+(9576776977/10000000000 : ℝ)*X 1 1+(-543831347/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1814402003/2000000000 : ℝ)*X 2 0+(62736923/10000000000 : ℝ)*X 2 1+(977178311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3539067733/5000000000 : ℝ)*X 0 0+(4281979583/10000000000 : ℝ)*X 0 1+(374523897/5000000000 : ℝ)*X 0 2+(3539067733/5000000000 : ℝ)*X 1 0+(4281979583/10000000000 : ℝ)*X 1 1+(374523897/5000000000 : ℝ)*X 1 2+(3539067733/5000000000 : ℝ)*X 2 0+(4281979583/10000000000 : ℝ)*X 2 1+(374523897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1117154237/5000000000 : ℝ)*X 0 0+(8185656777/10000000000 : ℝ)*X 0 1+(789270647/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((156710853/10000000000 : ℝ)*X 1 0+(8700194729/10000000000 : ℝ)*X 1 1+(-310911381/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((2105198863/2500000000 : ℝ)*X 2 0+(5665663/10000000000 : ℝ)*X 2 1+(2934593897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((3997750911/5000000000 : ℝ)*X 0 0+(2706563109/10000000000 : ℝ)*X 0 1+(1345600839/10000000000 : ℝ)*X 0 2+(3997750911/5000000000 : ℝ)*X 1 0+(2706563109/10000000000 : ℝ)*X 1 1+(1345600839/10000000000 : ℝ)*X 1 2+(3997750911/5000000000 : ℝ)*X 2 0+(2706563109/10000000000 : ℝ)*X 2 1+(1345600839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-4779103/2000000000 : ℝ)*X 0 0+(474474037/500000000 : ℝ)*X 0 1+(1249038933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((8889/5000000000 : ℝ)*X 1 0+(1589025571/2500000000 : ℝ)*X 1 1+(-5403486433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((8777399199/10000000000 : ℝ)*X 2 0+(15273933/10000000000 : ℝ)*X 2 1+(242213087/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((8558125163/10000000000 : ℝ)*X 0 0+(1341758401/5000000000 : ℝ)*X 0 1+(35813809/2000000000 : ℝ)*X 0 2+(8558125163/10000000000 : ℝ)*X 1 0+(1341758401/5000000000 : ℝ)*X 1 1+(35813809/2000000000 : ℝ)*X 1 2+(8558125163/10000000000 : ℝ)*X 2 0+(1341758401/5000000000 : ℝ)*X 2 1+(35813809/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((601/800 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(601/800 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10244387770854643274001/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (272934822433/250000000000 : ℝ)*(base5) + (1761338809009/500000000000 : ℝ)*(base7) + (349068889737/1000000000000 : ℝ)*(base34) + (274996359699/250000000000 : ℝ)*(base43) + (677042327199/200000000000 : ℝ)*(base53) + (4904283551739/1000000000000 : ℝ)*(major_s0_0) + (4153367002679/1000000000000 : ℝ)*(major_s0_1) + (1868140805481/1000000000000 : ℝ)*(major_s0_2) + (10632669/200000000000 : ℝ)*(sp_s0_1) + (3365662671/1000000000000 : ℝ)*(sp_s0_7) + (1452366827859/1000000000000 : ℝ)*(sp_s0_8) + (2414687044217/500000000000 : ℝ)*(sp_s0_9) + (2772748251593/500000000000 : ℝ)*(sp_s0_13) + (113897/10000000000 : ℝ)*(sp_s0_23) + (865906766159/250000000000 : ℝ)*(f.failure) + (2418815813599/500000000000 : ℝ)*(f.sum) + (6883574257347/100000000000000000000000000 : ℝ)*base62 + (12911903942573/100000000000000000000000000 : ℝ)*base65 + (404267263489493/1000000000000000000000000000 : ℝ)*base66 + (11680745442653/100000000000000000000000000 : ℝ)*base69 + (304739288559473/2000000000000000000000000000 : ℝ)*base70 + (20770301010927/2000000000000000000000000000 : ℝ)*base73 + (895444257/5000000000000000000000 : ℝ)*base75 + (13222918308013/2000000000000000000000000000 : ℝ)*base76 + (98474360641807/2000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (4019/3125000000000000 : ℝ)*base86 + (447/1562500000000000 : ℝ)*base88 + (4019/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((97087/100000 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(97087/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8807880585167862273009/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104462356051/125000000000 : ℝ)*(base5) + (1828233185507/500000000000 : ℝ)*(base7) + (181519011201/1000000000000 : ℝ)*(base34) + (2187853330547/1000000000000 : ℝ)*(base53) + (5746803177297/1000000000000 : ℝ)*(major_s0_0) + (2964161094249/500000000000 : ℝ)*(major_s0_1) + (116889651811/31250000000 : ℝ)*(major_s0_2) + (12648387/250000000000 : ℝ)*(sp_s0_6) + (78363/500000000000 : ℝ)*(sp_s0_13) + (3289418784739/1000000000000 : ℝ)*(sp_s0_14) + (173546889797/50000000000 : ℝ)*(sp_s0_15) + (6494327018237/1000000000000 : ℝ)*(sp_s0_16) + (1636961043693/250000000000 : ℝ)*(sp_s0_20) + (162956657/1000000000000 : ℝ)*(sp_s0_23) + (3908646413641/1000000000000 : ℝ)*(f.failure) + (5658791126487/1000000000000 : ℝ)*(f.sum) + (52832967821/390625000000000000000000 : ℝ)*base63 + (35891123439163/50000000000000000000000000 : ℝ)*base65 + (31939767308011/1000000000000000000000000000 : ℝ)*base66 + (789252771943/3125000000000000000000000 : ℝ)*base69 + (1605349487211021/2000000000000000000000000000 : ℝ)*base71 + (42541941730289/500000000000000000000000000 : ℝ)*base72 + (6155310729/10000000000000000000000 : ℝ)*base75 + (282929000977541/2000000000000000000000000000 : ℝ)*base77 + (175234324719347/1000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (5281/12500000000000000 : ℝ)*base86 + (5281/12500000000000000 : ℝ)*base88 + (17781/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((33549/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(33549/50000 : ℝ)*X 1 1+(1 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (633637247471875145073/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2945183008339/1000000000000 : ℝ)*(base5) + (7273429537329/1000000000000 : ℝ)*(base7) + (111294196439/250000000000 : ℝ)*(base34) + (445385523483/1000000000000 : ℝ)*(base43) + (3475161753263/500000000000 : ℝ)*(base53) + (254061/1000000000000 : ℝ)*(base59) + (4432201475221/500000000000 : ℝ)*(major_s0_0) + (4432097106357/500000000000 : ℝ)*(major_s0_1) + (2359256229671/1000000000000 : ℝ)*(major_s0_2) + (1162677/125000000000 : ℝ)*(sp_s0_2) + (17325467139/200000000000 : ℝ)*(sp_s0_21) + (488594822467/500000000000 : ℝ)*(sp_s0_22) + (104273013349/10000000000 : ℝ)*(sp_s0_23) + (1002103834403/100000000000 : ℝ)*(sp_s0_27) + (1227593720159/200000000000 : ℝ)*(f.failure) + (396375657573/50000000000 : ℝ)*(f.sum) + (41734244086877/100000000000000000000000000 : ℝ)*base62 + (30484591828441/50000000000000000000000000 : ℝ)*base64 + (56242859371401/2000000000000000000000000000 : ℝ)*base66 + (11909689856877/100000000000000000000000000 : ℝ)*base68 + (576427691501247/1000000000000000000000000000 : ℝ)*base70 + (255639682686477/2000000000000000000000000000 : ℝ)*base73 + (3866238583/5000000000000000000000 : ℝ)*base74 + (170217468470067/1000000000000000000000000000 : ℝ)*base76 + (76813009339859/1000000000000000000000000000 : ℝ)*base78 + (519/2500000000000000 : ℝ)*base86 + (1981/2500000000000000 : ℝ)*base89 + (1981/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (601/800 : ℝ) ^ (33/8 : ℝ) ≤ (1920839234951423883/6250000000000000000 : ℝ) := by
    have hpowers : (601/800 : ℝ)^33 ≤ (1920839234951423883/6250000000000000000 : ℝ)^8 := by
      have hnat : (601 : ℕ)^33*6250000000000000000^8 ≤ 1920839234951423883^8*800^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        601 800 1920839234951423883 6250000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (601/800 : ℝ)) (X := (1920839234951423883/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (8170839234951423883/6250000000000000000 : ℝ) ≤ (1067124141500873/1000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (8170839234951423883/6250000000000000000 : ℝ)^8 ≤ (1067124141500873/1000000000000000 : ℝ)^33 := by
      have hnat : (8170839234951423883 : ℕ)^8*1000000000000000^33 ≤ 1067124141500873^33*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8170839234951423883 6250000000000000000 1067124141500873 1000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1067124141500873/1000000000000000 : ℝ)) (X := (8170839234951423883/6250000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (5045839234951423883/3125000000000000000 : ℝ) ≤ (5615836587234169/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (5045839234951423883/3125000000000000000 : ℝ)^8 ≤ (5615836587234169/5000000000000000 : ℝ)^33 := by
      have hnat : (5045839234951423883 : ℕ)^8*5000000000000000^33 ≤ 5615836587234169^33*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5045839234951423883 3125000000000000000 5615836587234169 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5615836587234169/5000000000000000 : ℝ)) (X := (5045839234951423883/3125000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(67124141500873/751250000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(70053969932451/939062500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (601/800 : ℝ)) (alpha := (67124141500873/751250000000000 : ℝ)) (beta := (70053969932451/939062500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![0, 2, 1], ![1, 2, 0]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (601/800 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(67124141500873/751250000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(70053969932451/939062500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (97087/100000 : ℝ) ^ (33/8 : ℝ) ≤ (44259801893900557349/50000000000000000000 : ℝ) := by
    have hpowers : (97087/100000 : ℝ)^33 ≤ (44259801893900557349/50000000000000000000 : ℝ)^8 := by
      have hnat : (97087 : ℕ)^33*50000000000000000000^8 ≤ 44259801893900557349^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        97087 100000 44259801893900557349 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (97087/100000 : ℝ)) (X := (44259801893900557349/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (94259801893900557349/50000000000000000000 : ℝ) ≤ (2915366130499647/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (94259801893900557349/50000000000000000000 : ℝ)^8 ≤ (2915366130499647/2500000000000000 : ℝ)^33 := by
      have hnat : (94259801893900557349 : ℕ)^8*2500000000000000^33 ≤ 2915366130499647^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        94259801893900557349 50000000000000000000 2915366130499647 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2915366130499647/2500000000000000 : ℝ)) (X := (94259801893900557349/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (69259801893900557349/25000000000000000000 : ℝ) ≤ (12802144473816329/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (69259801893900557349/25000000000000000000 : ℝ)^8 ≤ (12802144473816329/10000000000000000 : ℝ)^33 := by
      have hnat : (69259801893900557349 : ℕ)^8*10000000000000000^33 ≤ 12802144473816329^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69259801893900557349 25000000000000000000 12802144473816329 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12802144473816329/10000000000000000 : ℝ)) (X := (69259801893900557349/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 0+X 2 0))+(415366130499647/2427175000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1140679951817741/9708700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (97087/100000 : ℝ)) (alpha := (415366130499647/2427175000000000 : ℝ)) (beta := (1140679951817741/9708700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![0, 2, 1], ![1, 2, 0]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (97087/100000 : ℝ)*((1 : ℝ)*pair X 1 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 0)+(415366130499647/2427175000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1140679951817741/9708700000000000 : ℝ)*((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (33549/50000 : ℝ) ^ (33/8 : ℝ) ≤ (19283106419418854627/100000000000000000000 : ℝ) := by
    have hpowers : (33549/50000 : ℝ)^33 ≤ (19283106419418854627/100000000000000000000 : ℝ)^8 := by
      have hnat : (33549 : ℕ)^33*100000000000000000000^8 ≤ 19283106419418854627^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33549 50000 19283106419418854627 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33549/50000 : ℝ)) (X := (19283106419418854627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (119283106419418854627/100000000000000000000 : ℝ) ≤ (10436733444600689/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (119283106419418854627/100000000000000000000 : ℝ)^8 ≤ (10436733444600689/10000000000000000 : ℝ)^33 := by
      have hnat : (119283106419418854627 : ℕ)^8*10000000000000000^33 ≤ 10436733444600689^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        119283106419418854627 100000000000000000000 10436733444600689 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10436733444600689/10000000000000000 : ℝ)) (X := (119283106419418854627/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (69283106419418854627/50000000000000000000 : ℝ) ≤ (10822838431191991/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (69283106419418854627/50000000000000000000 : ℝ)^8 ≤ (10822838431191991/10000000000000000 : ℝ)^33 := by
      have hnat : (69283106419418854627 : ℕ)^8*10000000000000000^33 ≤ 10822838431191991^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69283106419418854627 50000000000000000000 10822838431191991 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10822838431191991/10000000000000000 : ℝ)) (X := (69283106419418854627/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 1+X 1 1))+(436733444600689/6709800000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 1 2))+(193052493295651/3354900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (33549/50000 : ℝ)) (alpha := (436733444600689/6709800000000000 : ℝ)) (beta := (193052493295651/3354900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![0, 2, 1], ![1, 2, 0]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 2) ≤ (33549/50000 : ℝ)*((1 : ℝ)*pair X 2 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 1)+(436733444600689/6709800000000000 : ℝ)*((-1 : ℝ)*pair X 2 2)+(193052493295651/3354900000000000 : ℝ)*((-1 : ℝ)*pair X 2 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-59553/2500000000 : ℝ)*X 0 0+(491367087/500000000 : ℝ)*X 0 1+(34358891/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((-238287/10000000000 : ℝ)*X 1 0+(191060807/200000000 : ℝ)*X 1 1+(-567014087/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4725364191/5000000000 : ℝ)*X 2 0+(9461/5000000000 : ℝ)*X 2 1+(132600477/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2190774793/2500000000 : ℝ)*X 0 0+(198913469/1000000000 : ℝ)*X 0 1+(20322493/250000000 : ℝ)*X 0 2+(2190774793/2500000000 : ℝ)*X 1 0+(198913469/1000000000 : ℝ)*X 1 1+(20322493/250000000 : ℝ)*X 1 2+(2190774793/2500000000 : ℝ)*X 2 0+(198913469/1000000000 : ℝ)*X 2 1+(20322493/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c201245_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-38127/6250 : ℝ) < ((-18959/12500 : ℝ)*P 0+(-18959/12500 : ℝ)*P 1+(-18959/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-38127/6250 : ℝ) < (-8645868529784618180903016884289/1458732175000000000000000000000 : ℝ) := by norm_num
    linear_combination (29018224887/100000000000 : ℝ)*(base5) + (948730749597/1000000000000 : ℝ)*(base7) + (714883/1000000000000 : ℝ)*(base11) + (2023976221/125000000000 : ℝ)*(base40) + (415977073909/1000000000000 : ℝ)*(base53) + (32459/1000000000000 : ℝ)*(ratio_s0_0) + (7831/500000000000 : ℝ)*(ratio_s0_1) + (18959/12500 : ℝ)*(major_s1_0) + (1516720016439/1000000000000 : ℝ)*(major_s1_1) + (1100742926091/1000000000000 : ℝ)*(major_s1_2) + (482854256719/500000000000 : ℝ)*(sp_s1_0) + (965709211881/1000000000000 : ℝ)*(sp_s1_1) + (16718685511/10000000000 : ℝ)*(sp_s1_2) + (1658548500727/1000000000000 : ℝ)*(sp_s1_6) + (138168628579/100000000000 : ℝ)*(f.sum) + (394648260249213/1118300000000000000000000000 : ℝ)*base63 + (7982309218578201/9708700000000000000000000000 : ℝ)*base64 + (54697655357764047519/217144784200000000000000000000000 : ℝ)*base66 + (148119204907257/1118300000000000000000000000 : ℝ)*base68 + (32416168701/300500000000000000000000 : ℝ)*base71 + (333154367630517607/1344196600000000000000000000000 : ℝ)*base73 + (176379561/2500000000000000000000 : ℝ)*base74 + (1050499327073768401/5834928700000000000000000000000 : ℝ)*base76 + (12009612382588633/1458732175000000000000000000000 : ℝ)*base79 + (411/25000000000 : ℝ)*base81 + (411/25000000000 : ℝ)*base85 + (16439/1000000000000 : ℝ)*base88 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_repeated_p001_b092 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 323) (hlo : 245 ≤ c.val) (hhi : c.val < 246)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by
  have hc : c=245 := by omega
  rcases hc with rfl
  · exact collision_c201245 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 323) (hlo : 245 ≤ c.val) (hhi : c.val < 246)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b092 p hpa hpb c hlo hhi X hX

#print axioms solution

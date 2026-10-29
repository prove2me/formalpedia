-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b009
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:32.628918+00:00
-- url     : https://prove2.me/submissions/e0c2ed3b-fb4e-4199-b952-871c63ed49bf

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
theorem collision_support_c310019_s0_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-5464564393/10000000000 : ℝ)*x 0 + (1832959379/5000000000 : ℝ)*x 1 + (711914523/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5464564393/10000000000 : ℝ)^9 ≤ (22990129792419/50000000000000 : ℝ)^7 := by
    have hnat : (5464564393 : ℕ)^9*50000000000000^7 ≤ 22990129792419^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464564393 10000000000 22990129792419 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1832959379/5000000000 : ℝ)^9 ≤ (27520964269009/100000000000000 : ℝ)^7 := by
    have hnat : (1832959379 : ℕ)^9*100000000000000^7 ≤ 27520964269009^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1832959379 5000000000 27520964269009 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (711914523/2000000000 : ℝ)^9 ≤ (26498776126681/100000000000000 : ℝ)^7 := by
    have hnat : (711914523 : ℕ)^9*100000000000000^7 ≤ 26498776126681^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711914523 2000000000 26498776126681 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5464564393/10000000000 : ℝ), (1832959379/5000000000 : ℝ), (711914523/2000000000 : ℝ)] ![(22990129792419/50000000000000 : ℝ), (27520964269009/100000000000000 : ℝ), (26498776126681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5464564393/10000000000 : ℝ)|^9 ≤ (22990129792419/50000000000000 : ℝ)^7
        have hw : |(-5464564393/10000000000 : ℝ)|=(5464564393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1832959379/5000000000 : ℝ)|^9 ≤ (27520964269009/100000000000000 : ℝ)^7
        have hw : |(1832959379/5000000000 : ℝ)|=(1832959379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(711914523/2000000000 : ℝ)|^9 ≤ (26498776126681/100000000000000 : ℝ)^7
        have hw : |(711914523/2000000000 : ℝ)|=(711914523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s0_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3702360717/10000000000 : ℝ)*x 0 + (-2315233731/10000000000 : ℝ)*x 1 + (6448217729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3702360717/10000000000 : ℝ)^9 ≤ (27873206846399/100000000000000 : ℝ)^7 := by
    have hnat : (3702360717 : ℕ)^9*100000000000000^7 ≤ 27873206846399^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3702360717 10000000000 27873206846399 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2315233731/10000000000 : ℝ)^9 ≤ (15242300169481/100000000000000 : ℝ)^7 := by
    have hnat : (2315233731 : ℕ)^9*100000000000000^7 ≤ 15242300169481^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2315233731 10000000000 15242300169481 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6448217729/10000000000 : ℝ)^9 ≤ (56884492969001/100000000000000 : ℝ)^7 := by
    have hnat : (6448217729 : ℕ)^9*100000000000000^7 ≤ 56884492969001^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6448217729 10000000000 56884492969001 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3702360717/10000000000 : ℝ), (-2315233731/10000000000 : ℝ), (6448217729/10000000000 : ℝ)] ![(27873206846399/100000000000000 : ℝ), (15242300169481/100000000000000 : ℝ), (56884492969001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3702360717/10000000000 : ℝ)|^9 ≤ (27873206846399/100000000000000 : ℝ)^7
        have hw : |(3702360717/10000000000 : ℝ)|=(3702360717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2315233731/10000000000 : ℝ)|^9 ≤ (15242300169481/100000000000000 : ℝ)^7
        have hw : |(-2315233731/10000000000 : ℝ)|=(2315233731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6448217729/10000000000 : ℝ)|^9 ≤ (56884492969001/100000000000000 : ℝ)^7
        have hw : |(6448217729/10000000000 : ℝ)|=(6448217729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s0_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (435932287/1000000000 : ℝ)*x 0 + (2723730247/5000000000 : ℝ)*x 1 + (-1419813657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435932287/1000000000 : ℝ)^9 ≤ (6877425569643/20000000000000 : ℝ)^7 := by
    have hnat : (435932287 : ℕ)^9*20000000000000^7 ≤ 6877425569643^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435932287 1000000000 6877425569643 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2723730247/5000000000 : ℝ)^9 ≤ (11448826677561/25000000000000 : ℝ)^7 := by
    have hnat : (2723730247 : ℕ)^9*25000000000000^7 ≤ 11448826677561^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723730247 5000000000 11448826677561 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1419813657/5000000000 : ℝ)^9 ≤ (19817565425437/100000000000000 : ℝ)^7 := by
    have hnat : (1419813657 : ℕ)^9*100000000000000^7 ≤ 19817565425437^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419813657 5000000000 19817565425437 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435932287/1000000000 : ℝ), (2723730247/5000000000 : ℝ), (-1419813657/5000000000 : ℝ)] ![(6877425569643/20000000000000 : ℝ), (11448826677561/25000000000000 : ℝ), (19817565425437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435932287/1000000000 : ℝ)|^9 ≤ (6877425569643/20000000000000 : ℝ)^7
        have hw : |(435932287/1000000000 : ℝ)|=(435932287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2723730247/5000000000 : ℝ)|^9 ≤ (11448826677561/25000000000000 : ℝ)^7
        have hw : |(2723730247/5000000000 : ℝ)|=(2723730247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1419813657/5000000000 : ℝ)|^9 ≤ (19817565425437/100000000000000 : ℝ)^7
        have hw : |(-1419813657/5000000000 : ℝ)|=(1419813657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s0_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-708805503/1250000000 : ℝ)*x 0 + (400588011/1250000000 : ℝ)*x 1 + (1890094629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (708805503/1250000000 : ℝ)^9 ≤ (48219415768371/100000000000000 : ℝ)^7 := by
    have hnat : (708805503 : ℕ)^9*100000000000000^7 ≤ 48219415768371^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708805503 1250000000 48219415768371 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400588011/1250000000 : ℝ)^9 ≤ (23151785337647/100000000000000 : ℝ)^7 := by
    have hnat : (400588011 : ℕ)^9*100000000000000^7 ≤ 23151785337647^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400588011 1250000000 23151785337647 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1890094629/5000000000 : ℝ)^9 ≤ (447324982463/1562500000000 : ℝ)^7 := by
    have hnat : (1890094629 : ℕ)^9*1562500000000^7 ≤ 447324982463^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890094629 5000000000 447324982463 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-708805503/1250000000 : ℝ), (400588011/1250000000 : ℝ), (1890094629/5000000000 : ℝ)] ![(48219415768371/100000000000000 : ℝ), (23151785337647/100000000000000 : ℝ), (447324982463/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-708805503/1250000000 : ℝ)|^9 ≤ (48219415768371/100000000000000 : ℝ)^7
        have hw : |(-708805503/1250000000 : ℝ)|=(708805503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(400588011/1250000000 : ℝ)|^9 ≤ (23151785337647/100000000000000 : ℝ)^7
        have hw : |(400588011/1250000000 : ℝ)|=(400588011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1890094629/5000000000 : ℝ)|^9 ≤ (447324982463/1562500000000 : ℝ)^7
        have hw : |(1890094629/5000000000 : ℝ)|=(1890094629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s0_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1844515783/5000000000 : ℝ)*x 0 + (-1811423923/10000000000 : ℝ)*x 1 + (3410093921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1844515783/5000000000 : ℝ)^9 ≤ (5548850763111/20000000000000 : ℝ)^7 := by
    have hnat : (1844515783 : ℕ)^9*20000000000000^7 ≤ 5548850763111^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844515783 5000000000 5548850763111 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1811423923/10000000000 : ℝ)^9 ≤ (11117978801649/100000000000000 : ℝ)^7 := by
    have hnat : (1811423923 : ℕ)^9*100000000000000^7 ≤ 11117978801649^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811423923 10000000000 11117978801649 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3410093921/5000000000 : ℝ)^9 ≤ (61137767368269/100000000000000 : ℝ)^7 := by
    have hnat : (3410093921 : ℕ)^9*100000000000000^7 ≤ 61137767368269^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3410093921 5000000000 61137767368269 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1844515783/5000000000 : ℝ), (-1811423923/10000000000 : ℝ), (3410093921/5000000000 : ℝ)] ![(5548850763111/20000000000000 : ℝ), (11117978801649/100000000000000 : ℝ), (61137767368269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1844515783/5000000000 : ℝ)|^9 ≤ (5548850763111/20000000000000 : ℝ)^7
        have hw : |(1844515783/5000000000 : ℝ)|=(1844515783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1811423923/10000000000 : ℝ)|^9 ≤ (11117978801649/100000000000000 : ℝ)^7
        have hw : |(-1811423923/10000000000 : ℝ)|=(1811423923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3410093921/5000000000 : ℝ)|^9 ≤ (61137767368269/100000000000000 : ℝ)^7
        have hw : |(3410093921/5000000000 : ℝ)|=(3410093921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s0_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1974618203/5000000000 : ℝ)*x 0 + (958297/1600000 : ℝ)*x 1 + (-1316374959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1974618203/5000000000 : ℝ)^9 ≤ (30285250455983/100000000000000 : ℝ)^7 := by
    have hnat : (1974618203 : ℕ)^9*100000000000000^7 ≤ 30285250455983^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974618203 5000000000 30285250455983 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (958297/1600000 : ℝ)^9 ≤ (51733811140979/100000000000000 : ℝ)^7 := by
    have hnat : (958297 : ℕ)^9*100000000000000^7 ≤ 51733811140979^7*1600000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958297 1600000 51733811140979 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316374959/5000000000 : ℝ)^9 ≤ (2247617299077/12500000000000 : ℝ)^7 := by
    have hnat : (1316374959 : ℕ)^9*12500000000000^7 ≤ 2247617299077^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316374959 5000000000 2247617299077 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1974618203/5000000000 : ℝ), (958297/1600000 : ℝ), (-1316374959/5000000000 : ℝ)] ![(30285250455983/100000000000000 : ℝ), (51733811140979/100000000000000 : ℝ), (2247617299077/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1974618203/5000000000 : ℝ)|^9 ≤ (30285250455983/100000000000000 : ℝ)^7
        have hw : |(1974618203/5000000000 : ℝ)|=(1974618203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(958297/1600000 : ℝ)|^9 ≤ (51733811140979/100000000000000 : ℝ)^7
        have hw : |(958297/1600000 : ℝ)|=(958297/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1316374959/5000000000 : ℝ)|^9 ≤ (2247617299077/12500000000000 : ℝ)^7
        have hw : |(-1316374959/5000000000 : ℝ)|=(1316374959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s0_12 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1498928341/10000000000 : ℝ)*x 0 + (1550375601/2000000000 : ℝ)*x 1 + (1385590319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1498928341/10000000000 : ℝ)^9 ≤ (2178861876437/25000000000000 : ℝ)^7 := by
    have hnat : (1498928341 : ℕ)^9*25000000000000^7 ≤ 2178861876437^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498928341 10000000000 2178861876437 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1550375601/2000000000 : ℝ)^9 ≤ (72079025968839/100000000000000 : ℝ)^7 := by
    have hnat : (1550375601 : ℕ)^9*100000000000000^7 ≤ 72079025968839^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1550375601 2000000000 72079025968839 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1385590319/5000000000 : ℝ)^9 ≤ (3841105302379/20000000000000 : ℝ)^7 := by
    have hnat : (1385590319 : ℕ)^9*20000000000000^7 ≤ 3841105302379^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385590319 5000000000 3841105302379 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1498928341/10000000000 : ℝ), (1550375601/2000000000 : ℝ), (1385590319/5000000000 : ℝ)] ![(2178861876437/25000000000000 : ℝ), (72079025968839/100000000000000 : ℝ), (3841105302379/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1498928341/10000000000 : ℝ)|^9 ≤ (2178861876437/25000000000000 : ℝ)^7
        have hw : |(1498928341/10000000000 : ℝ)|=(1498928341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1550375601/2000000000 : ℝ)|^9 ≤ (72079025968839/100000000000000 : ℝ)^7
        have hw : |(1550375601/2000000000 : ℝ)|=(1550375601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1385590319/5000000000 : ℝ)|^9 ≤ (3841105302379/20000000000000 : ℝ)^7
        have hw : |(1385590319/5000000000 : ℝ)|=(1385590319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s0_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-5723728527/10000000000 : ℝ)*x 0 + (18298647/50000000 : ℝ)*x 1 + (1633713003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5723728527/10000000000 : ℝ)^9 ≤ (48802768960873/100000000000000 : ℝ)^7 := by
    have hnat : (5723728527 : ℕ)^9*100000000000000^7 ≤ 48802768960873^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5723728527 10000000000 48802768960873 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18298647/50000000 : ℝ)^9 ≤ (27461237904599/100000000000000 : ℝ)^7 := by
    have hnat : (18298647 : ℕ)^9*100000000000000^7 ≤ 27461237904599^7*50000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18298647 50000000 27461237904599 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1633713003/5000000000 : ℝ)^9 ≤ (2966999140147/12500000000000 : ℝ)^7 := by
    have hnat : (1633713003 : ℕ)^9*12500000000000^7 ≤ 2966999140147^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633713003 5000000000 2966999140147 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5723728527/10000000000 : ℝ), (18298647/50000000 : ℝ), (1633713003/5000000000 : ℝ)] ![(48802768960873/100000000000000 : ℝ), (27461237904599/100000000000000 : ℝ), (2966999140147/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5723728527/10000000000 : ℝ)|^9 ≤ (48802768960873/100000000000000 : ℝ)^7
        have hw : |(-5723728527/10000000000 : ℝ)|=(5723728527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(18298647/50000000 : ℝ)|^9 ≤ (27461237904599/100000000000000 : ℝ)^7
        have hw : |(18298647/50000000 : ℝ)|=(18298647/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1633713003/5000000000 : ℝ)|^9 ≤ (2966999140147/12500000000000 : ℝ)^7
        have hw : |(1633713003/5000000000 : ℝ)|=(1633713003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s0_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3885816551/10000000000 : ℝ)*x 0 + (-2285573931/10000000000 : ℝ)*x 1 + (1262448549/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3885816551/10000000000 : ℝ)^9 ≤ (14830695728807/50000000000000 : ℝ)^7 := by
    have hnat : (3885816551 : ℕ)^9*50000000000000^7 ≤ 14830695728807^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3885816551 10000000000 14830695728807 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2285573931/10000000000 : ℝ)^9 ≤ (14991706334231/100000000000000 : ℝ)^7 := by
    have hnat : (2285573931 : ℕ)^9*100000000000000^7 ≤ 14991706334231^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285573931 10000000000 14991706334231 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1262448549/2000000000 : ℝ)^9 ≤ (27673451095029/50000000000000 : ℝ)^7 := by
    have hnat : (1262448549 : ℕ)^9*50000000000000^7 ≤ 27673451095029^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262448549 2000000000 27673451095029 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3885816551/10000000000 : ℝ), (-2285573931/10000000000 : ℝ), (1262448549/2000000000 : ℝ)] ![(14830695728807/50000000000000 : ℝ), (14991706334231/100000000000000 : ℝ), (27673451095029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3885816551/10000000000 : ℝ)|^9 ≤ (14830695728807/50000000000000 : ℝ)^7
        have hw : |(3885816551/10000000000 : ℝ)|=(3885816551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2285573931/10000000000 : ℝ)|^9 ≤ (14991706334231/100000000000000 : ℝ)^7
        have hw : |(-2285573931/10000000000 : ℝ)|=(2285573931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1262448549/2000000000 : ℝ)|^9 ≤ (27673451095029/50000000000000 : ℝ)^7
        have hw : |(1262448549/2000000000 : ℝ)|=(1262448549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s0_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4103687059/10000000000 : ℝ)*x 0 + (2713766213/5000000000 : ℝ)*x 1 + (-786378541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4103687059/10000000000 : ℝ)^9 ≤ (31816513515109/100000000000000 : ℝ)^7 := by
    have hnat : (4103687059 : ℕ)^9*100000000000000^7 ≤ 31816513515109^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4103687059 10000000000 31816513515109 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713766213/5000000000 : ℝ)^9 ≤ (45580023913403/100000000000000 : ℝ)^7 := by
    have hnat : (2713766213 : ℕ)^9*100000000000000^7 ≤ 45580023913403^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713766213 5000000000 45580023913403 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (786378541/2500000000 : ℝ)^9 ≤ (11301731272673/50000000000000 : ℝ)^7 := by
    have hnat : (786378541 : ℕ)^9*50000000000000^7 ≤ 11301731272673^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786378541 2500000000 11301731272673 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4103687059/10000000000 : ℝ), (2713766213/5000000000 : ℝ), (-786378541/2500000000 : ℝ)] ![(31816513515109/100000000000000 : ℝ), (45580023913403/100000000000000 : ℝ), (11301731272673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4103687059/10000000000 : ℝ)|^9 ≤ (31816513515109/100000000000000 : ℝ)^7
        have hw : |(4103687059/10000000000 : ℝ)|=(4103687059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713766213/5000000000 : ℝ)|^9 ≤ (45580023913403/100000000000000 : ℝ)^7
        have hw : |(2713766213/5000000000 : ℝ)|=(2713766213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-786378541/2500000000 : ℝ)|^9 ≤ (11301731272673/50000000000000 : ℝ)^7
        have hw : |(-786378541/2500000000 : ℝ)|=(786378541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s0_19 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (848864857/5000000000 : ℝ)*x 0 + (6712797157/10000000000 : ℝ)*x 1 + (3906874223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848864857/5000000000 : ℝ)^9 ≤ (255723712841/2500000000000 : ℝ)^7 := by
    have hnat : (848864857 : ℕ)^9*2500000000000^7 ≤ 255723712841^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848864857 5000000000 255723712841 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6712797157/10000000000 : ℝ)^9 ≤ (59902836602653/100000000000000 : ℝ)^7 := by
    have hnat : (6712797157 : ℕ)^9*100000000000000^7 ≤ 59902836602653^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6712797157 10000000000 59902836602653 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3906874223/10000000000 : ℝ)^9 ≤ (2986821487189/10000000000000 : ℝ)^7 := by
    have hnat : (3906874223 : ℕ)^9*10000000000000^7 ≤ 2986821487189^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3906874223 10000000000 2986821487189 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848864857/5000000000 : ℝ), (6712797157/10000000000 : ℝ), (3906874223/10000000000 : ℝ)] ![(255723712841/2500000000000 : ℝ), (59902836602653/100000000000000 : ℝ), (2986821487189/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848864857/5000000000 : ℝ)|^9 ≤ (255723712841/2500000000000 : ℝ)^7
        have hw : |(848864857/5000000000 : ℝ)|=(848864857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6712797157/10000000000 : ℝ)|^9 ≤ (59902836602653/100000000000000 : ℝ)^7
        have hw : |(6712797157/10000000000 : ℝ)|=(6712797157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3906874223/10000000000 : ℝ)|^9 ≤ (2986821487189/10000000000000 : ℝ)^7
        have hw : |(3906874223/10000000000 : ℝ)|=(3906874223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s0_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-5514474829/10000000000 : ℝ)*x 0 + (960295617/2500000000 : ℝ)*x 1 + (10383947/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5514474829/10000000000 : ℝ)^9 ≤ (23260455141493/50000000000000 : ℝ)^7 := by
    have hnat : (5514474829 : ℕ)^9*50000000000000^7 ≤ 23260455141493^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514474829 10000000000 23260455141493 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960295617/2500000000 : ℝ)^9 ≤ (7306016407909/25000000000000 : ℝ)^7 := by
    have hnat : (960295617 : ℕ)^9*25000000000000^7 ≤ 7306016407909^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960295617 2500000000 7306016407909 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10383947/31250000 : ℝ)^9 ≤ (3031878009301/12500000000000 : ℝ)^7 := by
    have hnat : (10383947 : ℕ)^9*12500000000000^7 ≤ 3031878009301^7*31250000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10383947 31250000 3031878009301 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5514474829/10000000000 : ℝ), (960295617/2500000000 : ℝ), (10383947/31250000 : ℝ)] ![(23260455141493/50000000000000 : ℝ), (7306016407909/25000000000000 : ℝ), (3031878009301/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5514474829/10000000000 : ℝ)|^9 ≤ (23260455141493/50000000000000 : ℝ)^7
        have hw : |(-5514474829/10000000000 : ℝ)|=(5514474829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(960295617/2500000000 : ℝ)|^9 ≤ (7306016407909/25000000000000 : ℝ)^7
        have hw : |(960295617/2500000000 : ℝ)|=(960295617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10383947/31250000 : ℝ)|^9 ≤ (3031878009301/12500000000000 : ℝ)^7
        have hw : |(10383947/31250000 : ℝ)|=(10383947/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s0_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7019167/20000000 : ℝ)*x 0 + (-2152810991/10000000000 : ℝ)*x 1 + (6729734237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7019167/20000000 : ℝ)^9 ≤ (26021276790331/100000000000000 : ℝ)^7 := by
    have hnat : (7019167 : ℕ)^9*100000000000000^7 ≤ 26021276790331^7*20000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7019167 20000000 26021276790331 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2152810991/10000000000 : ℝ)^9 ≤ (13881492402653/100000000000000 : ℝ)^7 := by
    have hnat : (2152810991 : ℕ)^9*100000000000000^7 ≤ 13881492402653^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152810991 10000000000 13881492402653 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6729734237/10000000000 : ℝ)^9 ≤ (60097230796259/100000000000000 : ℝ)^7 := by
    have hnat : (6729734237 : ℕ)^9*100000000000000^7 ≤ 60097230796259^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6729734237 10000000000 60097230796259 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7019167/20000000 : ℝ), (-2152810991/10000000000 : ℝ), (6729734237/10000000000 : ℝ)] ![(26021276790331/100000000000000 : ℝ), (13881492402653/100000000000000 : ℝ), (60097230796259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7019167/20000000 : ℝ)|^9 ≤ (26021276790331/100000000000000 : ℝ)^7
        have hw : |(7019167/20000000 : ℝ)|=(7019167/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2152810991/10000000000 : ℝ)|^9 ≤ (13881492402653/100000000000000 : ℝ)^7
        have hw : |(-2152810991/10000000000 : ℝ)|=(2152810991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6729734237/10000000000 : ℝ)|^9 ≤ (60097230796259/100000000000000 : ℝ)^7
        have hw : |(6729734237/10000000000 : ℝ)|=(6729734237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s0_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4844189597/10000000000 : ℝ)*x 0 + (4911613983/10000000000 : ℝ)*x 1 + (-1459484273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4844189597/10000000000 : ℝ)^9 ≤ (39380779968533/100000000000000 : ℝ)^7 := by
    have hnat : (4844189597 : ℕ)^9*100000000000000^7 ≤ 39380779968533^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4844189597 10000000000 39380779968533 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4911613983/10000000000 : ℝ)^9 ≤ (5010863711583/12500000000000 : ℝ)^7 := by
    have hnat : (4911613983 : ℕ)^9*12500000000000^7 ≤ 5010863711583^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4911613983 10000000000 5010863711583 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1459484273/5000000000 : ℝ)^9 ≤ (20532310322807/100000000000000 : ℝ)^7 := by
    have hnat : (1459484273 : ℕ)^9*100000000000000^7 ≤ 20532310322807^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459484273 5000000000 20532310322807 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4844189597/10000000000 : ℝ), (4911613983/10000000000 : ℝ), (-1459484273/5000000000 : ℝ)] ![(39380779968533/100000000000000 : ℝ), (5010863711583/12500000000000 : ℝ), (20532310322807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4844189597/10000000000 : ℝ)|^9 ≤ (39380779968533/100000000000000 : ℝ)^7
        have hw : |(4844189597/10000000000 : ℝ)|=(4844189597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4911613983/10000000000 : ℝ)|^9 ≤ (5010863711583/12500000000000 : ℝ)^7
        have hw : |(4911613983/10000000000 : ℝ)|=(4911613983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1459484273/5000000000 : ℝ)|^9 ≤ (20532310322807/100000000000000 : ℝ)^7
        have hw : |(-1459484273/5000000000 : ℝ)|=(1459484273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s0_25 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1351139197/10000000000 : ℝ)*x 0 + (199379679/250000000 : ℝ)*x 1 + (2590850941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1351139197/10000000000 : ℝ)^9 ≤ (7626559998911/100000000000000 : ℝ)^7 := by
    have hnat : (1351139197 : ℕ)^9*100000000000000^7 ≤ 7626559998911^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351139197 10000000000 7626559998911 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199379679/250000000 : ℝ)^9 ≤ (37379789804657/50000000000000 : ℝ)^7 := by
    have hnat : (199379679 : ℕ)^9*50000000000000^7 ≤ 37379789804657^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199379679 250000000 37379789804657 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590850941/10000000000 : ℝ)^9 ≤ (17613860386669/100000000000000 : ℝ)^7 := by
    have hnat : (2590850941 : ℕ)^9*100000000000000^7 ≤ 17613860386669^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590850941 10000000000 17613860386669 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1351139197/10000000000 : ℝ), (199379679/250000000 : ℝ), (2590850941/10000000000 : ℝ)] ![(7626559998911/100000000000000 : ℝ), (37379789804657/50000000000000 : ℝ), (17613860386669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1351139197/10000000000 : ℝ)|^9 ≤ (7626559998911/100000000000000 : ℝ)^7
        have hw : |(1351139197/10000000000 : ℝ)|=(1351139197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(199379679/250000000 : ℝ)|^9 ≤ (37379789804657/50000000000000 : ℝ)^7
        have hw : |(199379679/250000000 : ℝ)|=(199379679/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590850941/10000000000 : ℝ)|^9 ≤ (17613860386669/100000000000000 : ℝ)^7
        have hw : |(2590850941/10000000000 : ℝ)|=(2590850941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-483682227/1000000000 : ℝ)*x 0 + (3955596451/10000000000 : ℝ)*x 1 + (3955623049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (483682227/1000000000 : ℝ)^9 ≤ (39303791940629/100000000000000 : ℝ)^7 := by
    have hnat : (483682227 : ℕ)^9*100000000000000^7 ≤ 39303791940629^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483682227 1000000000 39303791940629 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3955596451/10000000000 : ℝ)^9 ≤ (9711351309/32000000000 : ℝ)^7 := by
    have hnat : (3955596451 : ℕ)^9*32000000000^7 ≤ 9711351309^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3955596451 10000000000 9711351309 32000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3955623049/10000000000 : ℝ)^9 ≤ (6069647041811/20000000000000 : ℝ)^7 := by
    have hnat : (3955623049 : ℕ)^9*20000000000000^7 ≤ 6069647041811^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3955623049 10000000000 6069647041811 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-483682227/1000000000 : ℝ), (3955596451/10000000000 : ℝ), (3955623049/10000000000 : ℝ)] ![(39303791940629/100000000000000 : ℝ), (9711351309/32000000000 : ℝ), (6069647041811/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-483682227/1000000000 : ℝ)|^9 ≤ (39303791940629/100000000000000 : ℝ)^7
        have hw : |(-483682227/1000000000 : ℝ)|=(483682227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3955596451/10000000000 : ℝ)|^9 ≤ (9711351309/32000000000 : ℝ)^7
        have hw : |(3955596451/10000000000 : ℝ)|=(3955596451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3955623049/10000000000 : ℝ)|^9 ≤ (6069647041811/20000000000000 : ℝ)^7
        have hw : |(3955623049/10000000000 : ℝ)|=(3955623049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4093982709/10000000000 : ℝ)*x 0 + (-418511953/1250000000 : ℝ)*x 1 + (526083597/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4093982709/10000000000 : ℝ)^9 ≤ (31719809957871/100000000000000 : ℝ)^7 := by
    have hnat : (4093982709 : ℕ)^9*100000000000000^7 ≤ 31719809957871^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4093982709 10000000000 31719809957871 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (418511953/1250000000 : ℝ)^9 ≤ (4898417601661/20000000000000 : ℝ)^7 := by
    have hnat : (418511953 : ℕ)^9*20000000000000^7 ≤ 4898417601661^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418511953 1250000000 4898417601661 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526083597/1000000000 : ℝ)^9 ≤ (1368378187983/3125000000000 : ℝ)^7 := by
    have hnat : (526083597 : ℕ)^9*3125000000000^7 ≤ 1368378187983^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526083597 1000000000 1368378187983 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4093982709/10000000000 : ℝ), (-418511953/1250000000 : ℝ), (526083597/1000000000 : ℝ)] ![(31719809957871/100000000000000 : ℝ), (4898417601661/20000000000000 : ℝ), (1368378187983/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4093982709/10000000000 : ℝ)|^9 ≤ (31719809957871/100000000000000 : ℝ)^7
        have hw : |(4093982709/10000000000 : ℝ)|=(4093982709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-418511953/1250000000 : ℝ)|^9 ≤ (4898417601661/20000000000000 : ℝ)^7
        have hw : |(-418511953/1250000000 : ℝ)|=(418511953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526083597/1000000000 : ℝ)|^9 ≤ (1368378187983/3125000000000 : ℝ)^7
        have hw : |(526083597/1000000000 : ℝ)|=(526083597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4093962533/10000000000 : ℝ)*x 0 + (1315212367/2500000000 : ℝ)*x 1 + (-837025409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4093962533/10000000000 : ℝ)^9 ≤ (31719608972797/100000000000000 : ℝ)^7 := by
    have hnat : (4093962533 : ℕ)^9*100000000000000^7 ≤ 31719608972797^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4093962533 10000000000 31719608972797 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315212367/2500000000 : ℝ)^9 ≤ (21894123232373/50000000000000 : ℝ)^7 := by
    have hnat : (1315212367 : ℕ)^9*50000000000000^7 ≤ 21894123232373^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315212367 2500000000 21894123232373 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (837025409/2500000000 : ℝ)^9 ≤ (24492144552953/100000000000000 : ℝ)^7 := by
    have hnat : (837025409 : ℕ)^9*100000000000000^7 ≤ 24492144552953^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837025409 2500000000 24492144552953 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4093962533/10000000000 : ℝ), (1315212367/2500000000 : ℝ), (-837025409/2500000000 : ℝ)] ![(31719608972797/100000000000000 : ℝ), (21894123232373/50000000000000 : ℝ), (24492144552953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4093962533/10000000000 : ℝ)|^9 ≤ (31719608972797/100000000000000 : ℝ)^7
        have hw : |(4093962533/10000000000 : ℝ)|=(4093962533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315212367/2500000000 : ℝ)|^9 ≤ (21894123232373/50000000000000 : ℝ)^7
        have hw : |(1315212367/2500000000 : ℝ)|=(1315212367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-837025409/2500000000 : ℝ)|^9 ≤ (24492144552953/100000000000000 : ℝ)^7
        have hw : |(-837025409/2500000000 : ℝ)|=(837025409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310019_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3569002577/10000000000 : ℝ)*x 0 + (2293131063/5000000000 : ℝ)*x 1 + (4586227757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3569002577/10000000000 : ℝ)^9 ≤ (664726689261/2500000000000 : ℝ)^7 := by
    have hnat : (3569002577 : ℕ)^9*2500000000000^7 ≤ 664726689261^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3569002577 10000000000 664726689261 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2293131063/5000000000 : ℝ)^9 ≤ (7341128607159/20000000000000 : ℝ)^7 := by
    have hnat : (2293131063 : ℕ)^9*20000000000000^7 ≤ 7341128607159^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293131063 5000000000 7341128607159 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4586227757/10000000000 : ℝ)^9 ≤ (18352644688337/50000000000000 : ℝ)^7 := by
    have hnat : (4586227757 : ℕ)^9*50000000000000^7 ≤ 18352644688337^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4586227757 10000000000 18352644688337 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3569002577/10000000000 : ℝ), (2293131063/5000000000 : ℝ), (4586227757/10000000000 : ℝ)] ![(664726689261/2500000000000 : ℝ), (7341128607159/20000000000000 : ℝ), (18352644688337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3569002577/10000000000 : ℝ)|^9 ≤ (664726689261/2500000000000 : ℝ)^7
        have hw : |(3569002577/10000000000 : ℝ)|=(3569002577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2293131063/5000000000 : ℝ)|^9 ≤ (7341128607159/20000000000000 : ℝ)^7
        have hw : |(2293131063/5000000000 : ℝ)|=(2293131063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4586227757/10000000000 : ℝ)|^9 ≤ (18352644688337/50000000000000 : ℝ)^7
        have hw : |(4586227757/10000000000 : ℝ)|=(4586227757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310019 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]]) : False := by
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
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1137790796478959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (1716741708364597/10000000000000000 : ℝ)) (beta := (1137790796478959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1716741708364597/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1137790796478959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-5464564393/10000000000 : ℝ)*X 0 0+(1832959379/5000000000 : ℝ)*X 0 1+(711914523/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3702360717/10000000000 : ℝ)*X 1 0+(-2315233731/10000000000 : ℝ)*X 1 1+(6448217729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((435932287/1000000000 : ℝ)*X 2 0+(2723730247/5000000000 : ℝ)*X 2 1+(-1419813657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-708805503/1250000000 : ℝ)*X 0 0+(400588011/1250000000 : ℝ)*X 0 1+(1890094629/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1844515783/5000000000 : ℝ)*X 1 0+(-1811423923/10000000000 : ℝ)*X 1 1+(3410093921/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1974618203/5000000000 : ℝ)*X 2 0+(958297/1600000 : ℝ)*X 2 1+(-1316374959/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((1498928341/10000000000 : ℝ)*X 0 0+(1550375601/2000000000 : ℝ)*X 0 1+(1385590319/5000000000 : ℝ)*X 0 2+(1498928341/10000000000 : ℝ)*X 1 0+(1550375601/2000000000 : ℝ)*X 1 1+(1385590319/5000000000 : ℝ)*X 1 2+(1498928341/10000000000 : ℝ)*X 2 0+(1550375601/2000000000 : ℝ)*X 2 1+(1385590319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-5723728527/10000000000 : ℝ)*X 0 0+(18298647/50000000 : ℝ)*X 0 1+(1633713003/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((3885816551/10000000000 : ℝ)*X 1 0+(-2285573931/10000000000 : ℝ)*X 1 1+(1262448549/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4103687059/10000000000 : ℝ)*X 2 0+(2713766213/5000000000 : ℝ)*X 2 1+(-786378541/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((848864857/5000000000 : ℝ)*X 0 0+(6712797157/10000000000 : ℝ)*X 0 1+(3906874223/10000000000 : ℝ)*X 0 2+(848864857/5000000000 : ℝ)*X 1 0+(6712797157/10000000000 : ℝ)*X 1 1+(3906874223/10000000000 : ℝ)*X 1 2+(848864857/5000000000 : ℝ)*X 2 0+(6712797157/10000000000 : ℝ)*X 2 1+(3906874223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-5514474829/10000000000 : ℝ)*X 0 0+(960295617/2500000000 : ℝ)*X 0 1+(10383947/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((7019167/20000000 : ℝ)*X 1 0+(-2152810991/10000000000 : ℝ)*X 1 1+(6729734237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4844189597/10000000000 : ℝ)*X 2 0+(4911613983/10000000000 : ℝ)*X 2 1+(-1459484273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((1351139197/10000000000 : ℝ)*X 0 0+(199379679/250000000 : ℝ)*X 0 1+(2590850941/10000000000 : ℝ)*X 0 2+(1351139197/10000000000 : ℝ)*X 1 0+(199379679/250000000 : ℝ)*X 1 1+(2590850941/10000000000 : ℝ)*X 1 2+(1351139197/10000000000 : ℝ)*X 2 0+(199379679/250000000 : ℝ)*X 2 1+(2590850941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((25231/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(25231/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (26474394994047146466117/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2578045530773/1000000000000 : ℝ)*(base49) + (1153167688357/1000000000000 : ℝ)*(base50) + (2217610599/1562500000 : ℝ)*(base60) + (3700075559387/500000000000 : ℝ)*(major_s0_0) + (3700075559387/500000000000 : ℝ)*(major_s0_1) + (3700075559387/500000000000 : ℝ)*(major_s0_2) + (10936397/100000000000 : ℝ)*(sp_s0_0) + (2556587619057/250000000000 : ℝ)*(sp_s0_7) + (2556555631577/250000000000 : ℝ)*(sp_s0_8) + (5113184539823/500000000000 : ℝ)*(sp_s0_9) + (1143449654817/250000000000 : ℝ)*(sp_s0_12) + (11345069/125000000000 : ℝ)*(sp_s0_15) + (20124079/500000000000 : ℝ)*(sp_s0_19) + (237313889/1000000000000 : ℝ)*(sp_s0_21) + (2286919433713/500000000000 : ℝ)*(f.failure) + (5113229920099/500000000000 : ℝ)*(f.sum) + (297623398677961/2500000000000000000000000000 : ℝ)*base63 + (3368536334561867/5000000000000000000000000000 : ℝ)*base64 + (2553694196438133/5000000000000000000000000000 : ℝ)*base66 + (568717235822039/5000000000000000000000000000 : ℝ)*base68 + (552694952309957/1250000000000000000000000000 : ℝ)*base70 + (417277276938133/5000000000000000000000000000 : ℝ)*base73 + (2455826743822039/5000000000000000000000000000 : ℝ)*base74 + (3407155177177961/5000000000000000000000000000 : ℝ)*base76 + (19168331/5000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (27409/50000000000000000 : ℝ)*base87 + (27409/50000000000000000 : ℝ)*base89 + (27409/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2153/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2153/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (57508876905822369/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (2634269/1000000000000 : ℝ)*(base40) + (247242463919/200000000000 : ℝ)*(base49) + (298161428863/250000000000 : ℝ)*(base60) + (1279644606999/200000000000 : ℝ)*(major_s0_0) + (1279644606999/200000000000 : ℝ)*(major_s0_1) + (1279644606999/200000000000 : ℝ)*(major_s0_2) + (65864277/500000000000 : ℝ)*(sp_s0_2) + (184837437/1000000000000 : ℝ)*(sp_s0_7) + (16967/62500000000 : ℝ)*(sp_s0_8) + (4420841970281/500000000000 : ℝ)*(sp_s0_13) + (8841868506527/1000000000000 : ℝ)*(sp_s0_14) + (1768336340587/200000000000 : ℝ)*(sp_s0_15) + (3954573458057/1000000000000 : ℝ)*(sp_s0_19) + (55346509/1000000000000 : ℝ)*(sp_s0_22) + (3954573458057/1000000000000 : ℝ)*(f.failure) + (4420934388999/500000000000 : ℝ)*(f.sum) + (337234226385597/1000000000000000000000000000 : ℝ)*base63 + (344360686634041/2000000000000000000000000000 : ℝ)*base65 + (298183106565959/2000000000000000000000000000 : ℝ)*base67 + (236002915414403/2000000000000000000000000000 : ℝ)*base68 + (410891816612111/500000000000000000000000000 : ℝ)*base71 + (991258422365959/2000000000000000000000000000 : ℝ)*base72 + (642256786785597/2000000000000000000000000000 : ℝ)*base75 + (2074280013614403/2000000000000000000000000000 : ℝ)*base77 + (2308063501/10000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (83799/100000000000000000 : ℝ)*base86 + (83799/100000000000000000 : ℝ)*base88 + (83799/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(13927/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(13927/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1869365307474325734441/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1876666081073/1000000000000 : ℝ)*(base49) + (221999254049/500000000000 : ℝ)*(base50) + (106052947789/200000000000 : ℝ)*(base60) + (2944896586823/500000000000 : ℝ)*(major_s0_0) + (2944896586823/500000000000 : ℝ)*(major_s0_1) + (2944896586823/500000000000 : ℝ)*(major_s0_2) + (48647809/500000000000 : ℝ)*(sp_s0_1) + (48782889/1000000000000 : ℝ)*(sp_s0_2) + (10308163/100000000000 : ℝ)*(sp_s0_12) + (16590139/1000000000000 : ℝ)*(sp_s0_13) + (4069621216761/500000000000 : ℝ)*(sp_s0_20) + (2034790432011/250000000000 : ℝ)*(sp_s0_21) + (2034802560193/250000000000 : ℝ)*(sp_s0_22) + (3640223245001/1000000000000 : ℝ)*(sp_s0_25) + (3640326326631/1000000000000 : ℝ)*(f.failure) + (8139259023661/1000000000000 : ℝ)*(f.sum) + (314008691094669/2500000000000000000000000000 : ℝ)*base63 + (1309101666842743/5000000000000000000000000000 : ℝ)*base64 + (4322234233657257/5000000000000000000000000000 : ℝ)*base66 + (2966770616405331/5000000000000000000000000000 : ℝ)*base68 + (160519121984353/1250000000000000000000000000 : ℝ)*base70 + (2908659479342743/5000000000000000000000000000 : ℝ)*base72 + (2762775279594669/5000000000000000000000000000 : ℝ)*base75 + (93505873905331/5000000000000000000000000000 : ℝ)*base77 + (9488888223/10000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (9383/100000000000000000 : ℝ)*base87 + (9383/100000000000000000 : ℝ)*base89 + (9383/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (25231/100000 : ℝ) ^ (35/8 : ℝ) ≤ (15112742949580183/6250000000000000000 : ℝ) := by
    have hpowers : (25231/100000 : ℝ)^35 ≤ (15112742949580183/6250000000000000000 : ℝ)^8 := by
      have hnat : (25231 : ℕ)^35*6250000000000000000^8 ≤ 15112742949580183^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25231 100000 15112742949580183 6250000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25231/100000 : ℝ)) (X := (15112742949580183/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (6265112742949580183/6250000000000000000 : ℝ) ≤ (1000552179851219/1000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (6265112742949580183/6250000000000000000 : ℝ)^8 ≤ (1000552179851219/1000000000000000 : ℝ)^35 := by
      have hnat : (6265112742949580183 : ℕ)^8*1000000000000000^35 ≤ 1000552179851219^35*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6265112742949580183 6250000000000000000 1000552179851219 1000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000552179851219/1000000000000000 : ℝ)) (X := (6265112742949580183/6250000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (3140112742949580183/3125000000000000000 : ℝ) ≤ (10011033331355581/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3140112742949580183/3125000000000000000 : ℝ)^8 ≤ (10011033331355581/10000000000000000 : ℝ)^35 := by
      have hnat : (3140112742949580183 : ℕ)^8*10000000000000000^35 ≤ 10011033331355581^35*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3140112742949580183 3125000000000000000 10011033331355581 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011033331355581/10000000000000000 : ℝ)) (X := (3140112742949580183/3125000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(552179851219/252310000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(5511532843391/2523100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (25231/100000 : ℝ)) (alpha := (552179851219/252310000000000 : ℝ)) (beta := (5511532843391/2523100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (25231/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(552179851219/252310000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(5511532843391/2523100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (2153/50000 : ℝ) ^ (35/8 : ℝ) ≤ (2642493149989/2500000000000000000 : ℝ) := by
    have hpowers : (2153/50000 : ℝ)^35 ≤ (2642493149989/2500000000000000000 : ℝ)^8 := by
      have hnat : (2153 : ℕ)^35*2500000000000000000^8 ≤ 2642493149989^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2153 50000 2642493149989 2500000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2153/50000 : ℝ)) (X := (2642493149989/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (2500002642493149989/2500000000000000000 : ℝ) ≤ (10000002415992753/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (2500002642493149989/2500000000000000000 : ℝ)^8 ≤ (10000002415992753/10000000000000000 : ℝ)^35 := by
      have hnat : (2500002642493149989 : ℕ)^8*10000000000000000^35 ≤ 10000002415992753^35*2500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500002642493149989 2500000000000000000 10000002415992753 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002415992753/10000000000000000 : ℝ)) (X := (2500002642493149989/2500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (1250002642493149989/1250000000000000000 : ℝ) ≤ (2000000966396707/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (1250002642493149989/1250000000000000000 : ℝ)^8 ≤ (2000000966396707/2000000000000000 : ℝ)^35 := by
      have hnat : (1250002642493149989 : ℕ)^8*2000000000000000^35 ≤ 2000000966396707^35*1250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250002642493149989 1250000000000000000 2000000966396707 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000966396707/2000000000000000 : ℝ)) (X := (1250002642493149989/1250000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(2415992753/430600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1207995391/215300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (2153/50000 : ℝ)) (alpha := (2415992753/430600000000000 : ℝ)) (beta := (1207995391/215300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (2153/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(2415992753/430600000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1207995391/215300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13927/100000 : ℝ) ^ (35/8 : ℝ) ≤ (8981459121209447/50000000000000000000 : ℝ) := by
    have hpowers : (13927/100000 : ℝ)^35 ≤ (8981459121209447/50000000000000000000 : ℝ)^8 := by
      have hnat : (13927 : ℕ)^35*50000000000000000000^8 ≤ 8981459121209447^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13927 100000 8981459121209447 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13927/100000 : ℝ)) (X := (8981459121209447/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50008981459121209447/50000000000000000000 : ℝ) ≤ (10000410552544089/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50008981459121209447/50000000000000000000 : ℝ)^8 ≤ (10000410552544089/10000000000000000 : ℝ)^35 := by
      have hnat : (50008981459121209447 : ℕ)^8*10000000000000000^35 ≤ 10000410552544089^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008981459121209447 50000000000000000000 10000410552544089 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000410552544089/10000000000000000 : ℝ)) (X := (50008981459121209447/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25008981459121209447/25000000000000000000 : ℝ) ≤ (1250102631026453/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25008981459121209447/25000000000000000000 : ℝ)^8 ≤ (1250102631026453/1250000000000000 : ℝ)^35 := by
      have hnat : (25008981459121209447 : ℕ)^8*1250000000000000^35 ≤ 1250102631026453^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008981459121209447 25000000000000000000 1250102631026453 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250102631026453/1250000000000000 : ℝ)) (X := (25008981459121209447/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(410552544089/1392700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(82099133507/278540000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (13927/100000 : ℝ)) (alpha := (410552544089/1392700000000000 : ℝ)) (beta := (82099133507/278540000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (13927/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(410552544089/1392700000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(82099133507/278540000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-483682227/1000000000 : ℝ)*X 0 0+(3955596451/10000000000 : ℝ)*X 0 1+(3955623049/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4093982709/10000000000 : ℝ)*X 1 0+(-418511953/1250000000 : ℝ)*X 1 1+(526083597/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4093962533/10000000000 : ℝ)*X 2 0+(1315212367/2500000000 : ℝ)*X 2 1+(-837025409/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3569002577/10000000000 : ℝ)*X 0 0+(2293131063/5000000000 : ℝ)*X 0 1+(4586227757/10000000000 : ℝ)*X 0 2+(3569002577/10000000000 : ℝ)*X 1 0+(2293131063/5000000000 : ℝ)*X 1 1+(4586227757/10000000000 : ℝ)*X 1 2+(3569002577/10000000000 : ℝ)*X 2 0+(2293131063/5000000000 : ℝ)*X 2 1+(4586227757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310019_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-335379/50000 : ℝ) < ((-161793/100000 : ℝ)*P 0+(-161793/100000 : ℝ)*P 1+(-161793/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-335379/50000 : ℝ) < (-9941652447344576781662985470001/1499241550000000000000000000000 : ℝ) := by norm_num
    linear_combination (597867/1000000000000 : ℝ)*(base11) + (146223/1000000000000 : ℝ)*(base19) + (115241/200000000000 : ℝ)*(base23) + (641059973291/1000000000000 : ℝ)*(base49) + (356102173631/1000000000000 : ℝ)*(base50) + (5461/62500000000 : ℝ)*(base53) + (2807360509/40000000000 : ℝ)*(base59) + (177814851853/500000000000 : ℝ)*(base60) + (161793/100000 : ℝ)*(major_s1_0) + (161793/100000 : ℝ)*(major_s1_1) + (101120619539/62500000000 : ℝ)*(major_s1_2) + (442074610561/200000000000 : ℝ)*(sp_s1_0) + (2210373504449/1000000000000 : ℝ)*(sp_s1_1) + (552593290461/250000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (34537089657/15625000000 : ℝ)*(f.sum) + (173955898523409373/749620775000000000000000000000 : ℝ)*base63 + (50362012015199/139270000000000000000000000 : ℝ)*base65 + (112987912817/4306000000000000000000000 : ℝ)*base66 + (114089906194697/696350000000000000000000000 : ℝ)*base69 + (1082144219350843/6863127675781250000000000000 : ℝ)*base71 + (10611557249757/25231000000000000000000000 : ℝ)*base73 + (834532898911/5382500000000000000000000 : ℝ)*base75 + (5140369304197/15769375000000000000000000 : ℝ)*base76 + (4960733447869693/33951464375000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p010_b009 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 19 ≤ c.val) (hhi : c.val < 20)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=19 := by omega
  rcases hc with rfl
  · exact collision_c310019 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 19 ≤ c.val) (hhi : c.val < 20)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b009 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

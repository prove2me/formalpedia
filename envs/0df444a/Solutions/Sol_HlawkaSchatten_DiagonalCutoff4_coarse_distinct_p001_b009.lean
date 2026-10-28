-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b009
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:16:22.464294+00:00
-- url     : https://prove2.me/submissions/e457e6dc-0932-4921-974e-d72ace8af36a

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
theorem collision_support_c301019_s0_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5612564151/10000000000 : ℝ)*x 0 + (3769915441/10000000000 : ℝ)*x 1 + (3633393849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5612564151/10000000000 : ℝ)^65 ≤ (23239394795979/50000000000000 : ℝ)^49 := by
    have hnat : (5612564151 : ℕ)^65*50000000000000^49 ≤ 23239394795979^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5612564151 10000000000 23239394795979 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3769915441/10000000000 : ℝ)^65 ≤ (1713447993949/6250000000000 : ℝ)^49 := by
    have hnat : (3769915441 : ℕ)^65*6250000000000^49 ≤ 1713447993949^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3769915441 10000000000 1713447993949 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3633393849/10000000000 : ℝ)^65 ≤ (26106042484089/100000000000000 : ℝ)^49 := by
    have hnat : (3633393849 : ℕ)^65*100000000000000^49 ≤ 26106042484089^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3633393849 10000000000 26106042484089 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5612564151/10000000000 : ℝ), (3769915441/10000000000 : ℝ), (3633393849/10000000000 : ℝ)] ![(23239394795979/50000000000000 : ℝ), (1713447993949/6250000000000 : ℝ), (26106042484089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5612564151/10000000000 : ℝ)|^65 ≤ (23239394795979/50000000000000 : ℝ)^49
        have hw : |(-5612564151/10000000000 : ℝ)|=(5612564151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3769915441/10000000000 : ℝ)|^65 ≤ (1713447993949/6250000000000 : ℝ)^49
        have hw : |(3769915441/10000000000 : ℝ)|=(3769915441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3633393849/10000000000 : ℝ)|^65 ≤ (26106042484089/100000000000000 : ℝ)^49
        have hw : |(3633393849/10000000000 : ℝ)|=(3633393849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3805802967/10000000000 : ℝ)*x 0 + (-36722121/156250000 : ℝ)*x 1 + (6596955939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3805802967/10000000000 : ℝ)^65 ≤ (13880949629579/50000000000000 : ℝ)^49 := by
    have hnat : (3805802967 : ℕ)^65*50000000000000^49 ≤ 13880949629579^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3805802967 10000000000 13880949629579 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36722121/156250000 : ℝ)^65 ≤ (7323609140663/50000000000000 : ℝ)^49 := by
    have hnat : (36722121 : ℕ)^65*50000000000000^49 ≤ 7323609140663^49*156250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36722121 156250000 7323609140663 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6596955939/10000000000 : ℝ)^65 ≤ (2303635297871/4000000000000 : ℝ)^49 := by
    have hnat : (6596955939 : ℕ)^65*4000000000000^49 ≤ 2303635297871^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6596955939 10000000000 2303635297871 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3805802967/10000000000 : ℝ), (-36722121/156250000 : ℝ), (6596955939/10000000000 : ℝ)] ![(13880949629579/50000000000000 : ℝ), (7323609140663/50000000000000 : ℝ), (2303635297871/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3805802967/10000000000 : ℝ)|^65 ≤ (13880949629579/50000000000000 : ℝ)^49
        have hw : |(3805802967/10000000000 : ℝ)|=(3805802967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36722121/156250000 : ℝ)|^65 ≤ (7323609140663/50000000000000 : ℝ)^49
        have hw : |(-36722121/156250000 : ℝ)|=(36722121/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6596955939/10000000000 : ℝ)|^65 ≤ (2303635297871/4000000000000 : ℝ)^49
        have hw : |(6596955939/10000000000 : ℝ)|=(6596955939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2281093377/5000000000 : ℝ)*x 0 + (1092896459/2000000000 : ℝ)*x 1 + (-2953413243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2281093377/5000000000 : ℝ)^65 ≤ (17654386652479/50000000000000 : ℝ)^49 := by
    have hnat : (2281093377 : ℕ)^65*50000000000000^49 ≤ 17654386652479^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2281093377 5000000000 17654386652479 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092896459/2000000000 : ℝ)^65 ≤ (22429559754443/50000000000000 : ℝ)^49 := by
    have hnat : (1092896459 : ℕ)^65*50000000000000^49 ≤ 22429559754443^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092896459 2000000000 22429559754443 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2953413243/10000000000 : ℝ)^65 ≤ (1239506697719/6250000000000 : ℝ)^49 := by
    have hnat : (2953413243 : ℕ)^65*6250000000000^49 ≤ 1239506697719^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2953413243 10000000000 1239506697719 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2281093377/5000000000 : ℝ), (1092896459/2000000000 : ℝ), (-2953413243/10000000000 : ℝ)] ![(17654386652479/50000000000000 : ℝ), (22429559754443/50000000000000 : ℝ), (1239506697719/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2281093377/5000000000 : ℝ)|^65 ≤ (17654386652479/50000000000000 : ℝ)^49
        have hw : |(2281093377/5000000000 : ℝ)|=(2281093377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092896459/2000000000 : ℝ)|^65 ≤ (22429559754443/50000000000000 : ℝ)^49
        have hw : |(1092896459/2000000000 : ℝ)|=(1092896459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2953413243/10000000000 : ℝ)|^65 ≤ (1239506697719/6250000000000 : ℝ)^49
        have hw : |(-2953413243/10000000000 : ℝ)|=(2953413243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_4 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^65 ≤ (0 : ℝ)^49 := by
    have hnat : (0 : ℕ)^65*1^49 ≤ 0^49*1^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^65 ≤ (1 : ℝ)^49 := by
    have hnat : (1 : ℕ)^65*1^49 ≤ 1^49*1^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^65 ≤ (0 : ℝ)^49 := by
    have hnat : (0 : ℕ)^65*1^49 ≤ 0^49*1^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^65 ≤ (0 : ℝ)^49
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1 : ℝ)|^65 ≤ (1 : ℝ)^49
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^65 ≤ (0 : ℝ)^49
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (533320211/2500000000 : ℝ)*x 0 + (6837829067/10000000000 : ℝ)*x 1 + (1848908083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533320211/2500000000 : ℝ)^65 ≤ (12881358796527/100000000000000 : ℝ)^49 := by
    have hnat : (533320211 : ℕ)^65*100000000000000^49 ≤ 12881358796527^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533320211 2500000000 12881358796527 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6837829067/10000000000 : ℝ)^65 ≤ (30198404370983/50000000000000 : ℝ)^49 := by
    have hnat : (6837829067 : ℕ)^65*50000000000000^49 ≤ 30198404370983^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6837829067 10000000000 30198404370983 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1848908083/5000000000 : ℝ)^65 ≤ (3340229055757/12500000000000 : ℝ)^49 := by
    have hnat : (1848908083 : ℕ)^65*12500000000000^49 ≤ 3340229055757^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848908083 5000000000 3340229055757 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533320211/2500000000 : ℝ), (6837829067/10000000000 : ℝ), (1848908083/5000000000 : ℝ)] ![(12881358796527/100000000000000 : ℝ), (30198404370983/50000000000000 : ℝ), (3340229055757/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533320211/2500000000 : ℝ)|^65 ≤ (12881358796527/100000000000000 : ℝ)^49
        have hw : |(533320211/2500000000 : ℝ)|=(533320211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6837829067/10000000000 : ℝ)|^65 ≤ (30198404370983/50000000000000 : ℝ)^49
        have hw : |(6837829067/10000000000 : ℝ)|=(6837829067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1848908083/5000000000 : ℝ)|^65 ≤ (3340229055757/12500000000000 : ℝ)^49
        have hw : |(1848908083/5000000000 : ℝ)|=(1848908083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5821852313/10000000000 : ℝ)*x 0 + (1640028447/5000000000 : ℝ)*x 1 + (1936562829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5821852313/10000000000 : ℝ)^65 ≤ (9758351656321/20000000000000 : ℝ)^49 := by
    have hnat : (5821852313 : ℕ)^65*20000000000000^49 ≤ 9758351656321^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5821852313 10000000000 9758351656321 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1640028447/5000000000 : ℝ)^65 ≤ (2849127203407/12500000000000 : ℝ)^49 := by
    have hnat : (1640028447 : ℕ)^65*12500000000000^49 ≤ 2849127203407^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1640028447 5000000000 2849127203407 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1936562829/5000000000 : ℝ)^65 ≤ (14207612038637/50000000000000 : ℝ)^49 := by
    have hnat : (1936562829 : ℕ)^65*50000000000000^49 ≤ 14207612038637^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936562829 5000000000 14207612038637 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5821852313/10000000000 : ℝ), (1640028447/5000000000 : ℝ), (1936562829/5000000000 : ℝ)] ![(9758351656321/20000000000000 : ℝ), (2849127203407/12500000000000 : ℝ), (14207612038637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5821852313/10000000000 : ℝ)|^65 ≤ (9758351656321/20000000000000 : ℝ)^49
        have hw : |(-5821852313/10000000000 : ℝ)|=(5821852313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1640028447/5000000000 : ℝ)|^65 ≤ (2849127203407/12500000000000 : ℝ)^49
        have hw : |(1640028447/5000000000 : ℝ)|=(1640028447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1936562829/5000000000 : ℝ)|^65 ≤ (14207612038637/50000000000000 : ℝ)^49
        have hw : |(1936562829/5000000000 : ℝ)|=(1936562829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1885513293/5000000000 : ℝ)*x 0 + (-1801200397/10000000000 : ℝ)*x 1 + (699816253/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885513293/5000000000 : ℝ)^65 ≤ (27425887247241/100000000000000 : ℝ)^49 := by
    have hnat : (1885513293 : ℕ)^65*100000000000000^49 ≤ 27425887247241^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885513293 5000000000 27425887247241 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1801200397/10000000000 : ℝ)^65 ≤ (10291537223851/100000000000000 : ℝ)^49 := by
    have hnat : (1801200397 : ℕ)^65*100000000000000^49 ≤ 10291537223851^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1801200397 10000000000 10291537223851 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (699816253/1000000000 : ℝ)^65 ≤ (62282575515391/100000000000000 : ℝ)^49 := by
    have hnat : (699816253 : ℕ)^65*100000000000000^49 ≤ 62282575515391^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699816253 1000000000 62282575515391 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1885513293/5000000000 : ℝ), (-1801200397/10000000000 : ℝ), (699816253/1000000000 : ℝ)] ![(27425887247241/100000000000000 : ℝ), (10291537223851/100000000000000 : ℝ), (62282575515391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1885513293/5000000000 : ℝ)|^65 ≤ (27425887247241/100000000000000 : ℝ)^49
        have hw : |(1885513293/5000000000 : ℝ)|=(1885513293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1801200397/10000000000 : ℝ)|^65 ≤ (10291537223851/100000000000000 : ℝ)^49
        have hw : |(-1801200397/10000000000 : ℝ)|=(1801200397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(699816253/1000000000 : ℝ)|^65 ≤ (62282575515391/100000000000000 : ℝ)^49
        have hw : |(699816253/1000000000 : ℝ)|=(699816253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4104674517/10000000000 : ℝ)*x 0 + (3029083689/5000000000 : ℝ)*x 1 + (-1365366153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4104674517/10000000000 : ℝ)^65 ≤ (7672597203221/25000000000000 : ℝ)^49 := by
    have hnat : (4104674517 : ℕ)^65*25000000000000^49 ≤ 7672597203221^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4104674517 10000000000 7672597203221 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3029083689/5000000000 : ℝ)^65 ≤ (51436218089741/100000000000000 : ℝ)^49 := by
    have hnat : (3029083689 : ℕ)^65*100000000000000^49 ≤ 51436218089741^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3029083689 5000000000 51436218089741 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365366153/5000000000 : ℝ)^65 ≤ (1117087068109/6250000000000 : ℝ)^49 := by
    have hnat : (1365366153 : ℕ)^65*6250000000000^49 ≤ 1117087068109^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365366153 5000000000 1117087068109 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4104674517/10000000000 : ℝ), (3029083689/5000000000 : ℝ), (-1365366153/5000000000 : ℝ)] ![(7672597203221/25000000000000 : ℝ), (51436218089741/100000000000000 : ℝ), (1117087068109/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4104674517/10000000000 : ℝ)|^65 ≤ (7672597203221/25000000000000 : ℝ)^49
        have hw : |(4104674517/10000000000 : ℝ)|=(4104674517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3029083689/5000000000 : ℝ)|^65 ≤ (51436218089741/100000000000000 : ℝ)^49
        have hw : |(3029083689/5000000000 : ℝ)|=(3029083689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1365366153/5000000000 : ℝ)|^65 ≤ (1117087068109/6250000000000 : ℝ)^49
        have hw : |(-1365366153/5000000000 : ℝ)|=(1365366153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_12 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (396804597/2500000000 : ℝ)*x 0 + (3884229707/5000000000 : ℝ)*x 1 + (736378543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396804597/2500000000 : ℝ)^65 ≤ (8702020336289/100000000000000 : ℝ)^49 := by
    have hnat : (396804597 : ℕ)^65*100000000000000^49 ≤ 8702020336289^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396804597 2500000000 8702020336289 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3884229707/5000000000 : ℝ)^65 ≤ (71536203710717/100000000000000 : ℝ)^49 := by
    have hnat : (3884229707 : ℕ)^65*100000000000000^49 ≤ 71536203710717^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3884229707 5000000000 71536203710717 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (736378543/2500000000 : ℝ)^65 ≤ (19761775945091/100000000000000 : ℝ)^49 := by
    have hnat : (736378543 : ℕ)^65*100000000000000^49 ≤ 19761775945091^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736378543 2500000000 19761775945091 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(396804597/2500000000 : ℝ), (3884229707/5000000000 : ℝ), (736378543/2500000000 : ℝ)] ![(8702020336289/100000000000000 : ℝ), (71536203710717/100000000000000 : ℝ), (19761775945091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(396804597/2500000000 : ℝ)|^65 ≤ (8702020336289/100000000000000 : ℝ)^49
        have hw : |(396804597/2500000000 : ℝ)|=(396804597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3884229707/5000000000 : ℝ)|^65 ≤ (71536203710717/100000000000000 : ℝ)^49
        have hw : |(3884229707/5000000000 : ℝ)|=(3884229707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(736378543/2500000000 : ℝ)|^65 ≤ (19761775945091/100000000000000 : ℝ)^49
        have hw : |(736378543/2500000000 : ℝ)|=(736378543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5955517257/10000000000 : ℝ)*x 0 + (3753829521/10000000000 : ℝ)*x 1 + (3243493971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5955517257/10000000000 : ℝ)^65 ≤ (50283304393117/100000000000000 : ℝ)^49 := by
    have hnat : (5955517257 : ℕ)^65*100000000000000^49 ≤ 50283304393117^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5955517257 10000000000 50283304393117 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3753829521/10000000000 : ℝ)^65 ≤ (13630050424023/50000000000000 : ℝ)^49 := by
    have hnat : (3753829521 : ℕ)^65*50000000000000^49 ≤ 13630050424023^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3753829521 10000000000 13630050424023 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3243493971/10000000000 : ℝ)^65 ≤ (22456594735211/100000000000000 : ℝ)^49 := by
    have hnat : (3243493971 : ℕ)^65*100000000000000^49 ≤ 22456594735211^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3243493971 10000000000 22456594735211 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5955517257/10000000000 : ℝ), (3753829521/10000000000 : ℝ), (3243493971/10000000000 : ℝ)] ![(50283304393117/100000000000000 : ℝ), (13630050424023/50000000000000 : ℝ), (22456594735211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5955517257/10000000000 : ℝ)|^65 ≤ (50283304393117/100000000000000 : ℝ)^49
        have hw : |(-5955517257/10000000000 : ℝ)|=(5955517257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3753829521/10000000000 : ℝ)|^65 ≤ (13630050424023/50000000000000 : ℝ)^49
        have hw : |(3753829521/10000000000 : ℝ)|=(3753829521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3243493971/10000000000 : ℝ)|^65 ≤ (22456594735211/100000000000000 : ℝ)^49
        have hw : |(3243493971/10000000000 : ℝ)|=(3243493971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2037698301/5000000000 : ℝ)*x 0 + (-2314455049/10000000000 : ℝ)*x 1 + (1598389061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037698301/5000000000 : ℝ)^65 ≤ (3800042238451/12500000000000 : ℝ)^49 := by
    have hnat : (2037698301 : ℕ)^65*12500000000000^49 ≤ 3800042238451^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037698301 5000000000 3800042238451 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2314455049/10000000000 : ℝ)^65 ≤ (14352310181433/100000000000000 : ℝ)^49 := by
    have hnat : (2314455049 : ℕ)^65*100000000000000^49 ≤ 14352310181433^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2314455049 10000000000 14352310181433 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1598389061/2500000000 : ℝ)^65 ≤ (27623675947527/50000000000000 : ℝ)^49 := by
    have hnat : (1598389061 : ℕ)^65*50000000000000^49 ≤ 27623675947527^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1598389061 2500000000 27623675947527 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2037698301/5000000000 : ℝ), (-2314455049/10000000000 : ℝ), (1598389061/2500000000 : ℝ)] ![(3800042238451/12500000000000 : ℝ), (14352310181433/100000000000000 : ℝ), (27623675947527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2037698301/5000000000 : ℝ)|^65 ≤ (3800042238451/12500000000000 : ℝ)^49
        have hw : |(2037698301/5000000000 : ℝ)|=(2037698301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2314455049/10000000000 : ℝ)|^65 ≤ (14352310181433/100000000000000 : ℝ)^49
        have hw : |(-2314455049/10000000000 : ℝ)|=(2314455049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1598389061/2500000000 : ℝ)|^65 ≤ (27623675947527/50000000000000 : ℝ)^49
        have hw : |(1598389061/2500000000 : ℝ)|=(1598389061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4228175011/10000000000 : ℝ)*x 0 + (5435379141/10000000000 : ℝ)*x 1 + (-672072949/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4228175011/10000000000 : ℝ)^65 ≤ (7980322812773/25000000000000 : ℝ)^49 := by
    have hnat : (4228175011 : ℕ)^65*25000000000000^49 ≤ 7980322812773^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228175011 10000000000 7980322812773 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435379141/10000000000 : ℝ)^65 ≤ (11135617137723/25000000000000 : ℝ)^49 := by
    have hnat : (5435379141 : ℕ)^65*25000000000000^49 ≤ 11135617137723^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435379141 10000000000 11135617137723 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672072949/2000000000 : ℝ)^65 ≤ (11768120092813/50000000000000 : ℝ)^49 := by
    have hnat : (672072949 : ℕ)^65*50000000000000^49 ≤ 11768120092813^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672072949 2000000000 11768120092813 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4228175011/10000000000 : ℝ), (5435379141/10000000000 : ℝ), (-672072949/2000000000 : ℝ)] ![(7980322812773/25000000000000 : ℝ), (11135617137723/25000000000000 : ℝ), (11768120092813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4228175011/10000000000 : ℝ)|^65 ≤ (7980322812773/25000000000000 : ℝ)^49
        have hw : |(4228175011/10000000000 : ℝ)|=(4228175011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435379141/10000000000 : ℝ)|^65 ≤ (11135617137723/25000000000000 : ℝ)^49
        have hw : |(5435379141/10000000000 : ℝ)|=(5435379141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-672072949/2000000000 : ℝ)|^65 ≤ (11768120092813/50000000000000 : ℝ)^49
        have hw : |(-672072949/2000000000 : ℝ)|=(672072949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_19 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (331731731/2000000000 : ℝ)*x 0 + (1697489157/2500000000 : ℝ)*x 1 + (412962433/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331731731/2000000000 : ℝ)^65 ≤ (92253701633/1000000000000 : ℝ)^49 := by
    have hnat : (331731731 : ℕ)^65*1000000000000^49 ≤ 92253701633^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331731731 2000000000 92253701633 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1697489157/2500000000 : ℝ)^65 ≤ (29918266964141/50000000000000 : ℝ)^49 := by
    have hnat : (1697489157 : ℕ)^65*50000000000000^49 ≤ 29918266964141^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697489157 2500000000 29918266964141 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412962433/1000000000 : ℝ)^65 ≤ (30938095896821/100000000000000 : ℝ)^49 := by
    have hnat : (412962433 : ℕ)^65*100000000000000^49 ≤ 30938095896821^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412962433 1000000000 30938095896821 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331731731/2000000000 : ℝ), (1697489157/2500000000 : ℝ), (412962433/1000000000 : ℝ)] ![(92253701633/1000000000000 : ℝ), (29918266964141/50000000000000 : ℝ), (30938095896821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331731731/2000000000 : ℝ)|^65 ≤ (92253701633/1000000000000 : ℝ)^49
        have hw : |(331731731/2000000000 : ℝ)|=(331731731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1697489157/2500000000 : ℝ)|^65 ≤ (29918266964141/50000000000000 : ℝ)^49
        have hw : |(1697489157/2500000000 : ℝ)|=(1697489157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(412962433/1000000000 : ℝ)|^65 ≤ (30938095896821/100000000000000 : ℝ)^49
        have hw : |(412962433/1000000000 : ℝ)|=(412962433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1134036661/2000000000 : ℝ)*x 0 + (991275543/2500000000 : ℝ)*x 1 + (3364362239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1134036661/2000000000 : ℝ)^65 ≤ (5889101259403/12500000000000 : ℝ)^49 := by
    have hnat : (1134036661 : ℕ)^65*12500000000000^49 ≤ 5889101259403^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134036661 2000000000 5889101259403 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (991275543/2500000000 : ℝ)^65 ≤ (1832112583321/6250000000000 : ℝ)^49 := by
    have hnat : (991275543 : ℕ)^65*6250000000000^49 ≤ 1832112583321^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991275543 2500000000 1832112583321 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3364362239/10000000000 : ℝ)^65 ≤ (2946673572881/12500000000000 : ℝ)^49 := by
    have hnat : (3364362239 : ℕ)^65*12500000000000^49 ≤ 2946673572881^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3364362239 10000000000 2946673572881 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1134036661/2000000000 : ℝ), (991275543/2500000000 : ℝ), (3364362239/10000000000 : ℝ)] ![(5889101259403/12500000000000 : ℝ), (1832112583321/6250000000000 : ℝ), (2946673572881/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1134036661/2000000000 : ℝ)|^65 ≤ (5889101259403/12500000000000 : ℝ)^49
        have hw : |(-1134036661/2000000000 : ℝ)|=(1134036661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(991275543/2500000000 : ℝ)|^65 ≤ (1832112583321/6250000000000 : ℝ)^49
        have hw : |(991275543/2500000000 : ℝ)|=(991275543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3364362239/10000000000 : ℝ)|^65 ≤ (2946673572881/12500000000000 : ℝ)^49
        have hw : |(3364362239/10000000000 : ℝ)|=(3364362239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (721327521/2000000000 : ℝ)*x 0 + (-1085436611/5000000000 : ℝ)*x 1 + (6886294761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (721327521/2000000000 : ℝ)^65 ≤ (3231416438329/12500000000000 : ℝ)^49 := by
    have hnat : (721327521 : ℕ)^65*12500000000000^49 ≤ 3231416438329^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721327521 2000000000 3231416438329 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085436611/5000000000 : ℝ)^65 ≤ (13183335551897/100000000000000 : ℝ)^49 := by
    have hnat : (1085436611 : ℕ)^65*100000000000000^49 ≤ 13183335551897^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085436611 5000000000 13183335551897 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6886294761/10000000000 : ℝ)^65 ≤ (60965332927891/100000000000000 : ℝ)^49 := by
    have hnat : (6886294761 : ℕ)^65*100000000000000^49 ≤ 60965332927891^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6886294761 10000000000 60965332927891 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(721327521/2000000000 : ℝ), (-1085436611/5000000000 : ℝ), (6886294761/10000000000 : ℝ)] ![(3231416438329/12500000000000 : ℝ), (13183335551897/100000000000000 : ℝ), (60965332927891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(721327521/2000000000 : ℝ)|^65 ≤ (3231416438329/12500000000000 : ℝ)^49
        have hw : |(721327521/2000000000 : ℝ)|=(721327521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1085436611/5000000000 : ℝ)|^65 ≤ (13183335551897/100000000000000 : ℝ)^49
        have hw : |(-1085436611/5000000000 : ℝ)|=(1085436611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6886294761/10000000000 : ℝ)|^65 ≤ (60965332927891/100000000000000 : ℝ)^49
        have hw : |(6886294761/10000000000 : ℝ)|=(6886294761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5095944667/10000000000 : ℝ)*x 0 + (610488489/1250000000 : ℝ)*x 1 + (-1511820949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5095944667/10000000000 : ℝ)^65 ≤ (40890705809217/100000000000000 : ℝ)^49 := by
    have hnat : (5095944667 : ℕ)^65*100000000000000^49 ≤ 40890705809217^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5095944667 10000000000 40890705809217 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (610488489/1250000000 : ℝ)^65 ≤ (38649200709989/100000000000000 : ℝ)^49 := by
    have hnat : (610488489 : ℕ)^65*100000000000000^49 ≤ 38649200709989^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610488489 1250000000 38649200709989 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1511820949/5000000000 : ℝ)^65 ≤ (2046009346471/10000000000000 : ℝ)^49 := by
    have hnat : (1511820949 : ℕ)^65*10000000000000^49 ≤ 2046009346471^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1511820949 5000000000 2046009346471 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5095944667/10000000000 : ℝ), (610488489/1250000000 : ℝ), (-1511820949/5000000000 : ℝ)] ![(40890705809217/100000000000000 : ℝ), (38649200709989/100000000000000 : ℝ), (2046009346471/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5095944667/10000000000 : ℝ)|^65 ≤ (40890705809217/100000000000000 : ℝ)^49
        have hw : |(5095944667/10000000000 : ℝ)|=(5095944667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(610488489/1250000000 : ℝ)|^65 ≤ (38649200709989/100000000000000 : ℝ)^49
        have hw : |(610488489/1250000000 : ℝ)|=(610488489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1511820949/5000000000 : ℝ)|^65 ≤ (2046009346471/10000000000000 : ℝ)^49
        have hw : |(-1511820949/5000000000 : ℝ)|=(1511820949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s0_25 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (718012191/5000000000 : ℝ)*x 0 + (1000322329/1250000000 : ℝ)*x 1 + (1370928863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (718012191/5000000000 : ℝ)^65 ≤ (7619901279179/100000000000000 : ℝ)^49 := by
    have hnat : (718012191 : ℕ)^65*100000000000000^49 ≤ 7619901279179^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718012191 5000000000 7619901279179 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1000322329/1250000000 : ℝ)^65 ≤ (74410044886023/100000000000000 : ℝ)^49 := by
    have hnat : (1000322329 : ℕ)^65*100000000000000^49 ≤ 74410044886023^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000322329 1250000000 74410044886023 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370928863/5000000000 : ℝ)^65 ≤ (17970053823929/100000000000000 : ℝ)^49 := by
    have hnat : (1370928863 : ℕ)^65*100000000000000^49 ≤ 17970053823929^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370928863 5000000000 17970053823929 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(718012191/5000000000 : ℝ), (1000322329/1250000000 : ℝ), (1370928863/5000000000 : ℝ)] ![(7619901279179/100000000000000 : ℝ), (74410044886023/100000000000000 : ℝ), (17970053823929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(718012191/5000000000 : ℝ)|^65 ≤ (7619901279179/100000000000000 : ℝ)^49
        have hw : |(718012191/5000000000 : ℝ)|=(718012191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1000322329/1250000000 : ℝ)|^65 ≤ (74410044886023/100000000000000 : ℝ)^49
        have hw : |(1000322329/1250000000 : ℝ)|=(1000322329/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1370928863/5000000000 : ℝ)|^65 ≤ (17970053823929/100000000000000 : ℝ)^49
        have hw : |(1370928863/5000000000 : ℝ)|=(1370928863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2454658369/5000000000 : ℝ)*x 0 + (4089618041/10000000000 : ℝ)*x 1 + (2044887569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2454658369/5000000000 : ℝ)^65 ≤ (19458079443723/50000000000000 : ℝ)^49 := by
    have hnat : (2454658369 : ℕ)^65*50000000000000^49 ≤ 19458079443723^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2454658369 5000000000 19458079443723 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4089618041/10000000000 : ℝ)^65 ≤ (30541142401919/100000000000000 : ℝ)^49 := by
    have hnat : (4089618041 : ℕ)^65*100000000000000^49 ≤ 30541142401919^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4089618041 10000000000 30541142401919 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2044887569/5000000000 : ℝ)^65 ≤ (30542698691543/100000000000000 : ℝ)^49 := by
    have hnat : (2044887569 : ℕ)^65*100000000000000^49 ≤ 30542698691543^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044887569 5000000000 30542698691543 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2454658369/5000000000 : ℝ), (4089618041/10000000000 : ℝ), (2044887569/5000000000 : ℝ)] ![(19458079443723/50000000000000 : ℝ), (30541142401919/100000000000000 : ℝ), (30542698691543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2454658369/5000000000 : ℝ)|^65 ≤ (19458079443723/50000000000000 : ℝ)^49
        have hw : |(-2454658369/5000000000 : ℝ)|=(2454658369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4089618041/10000000000 : ℝ)|^65 ≤ (30541142401919/100000000000000 : ℝ)^49
        have hw : |(4089618041/10000000000 : ℝ)|=(4089618041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2044887569/5000000000 : ℝ)|^65 ≤ (30542698691543/100000000000000 : ℝ)^49
        have hw : |(2044887569/5000000000 : ℝ)|=(2044887569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s1_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4235671249/10000000000 : ℝ)*x 0 + (-1764224889/5000000000 : ℝ)*x 1 + (1320737169/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4235671249/10000000000 : ℝ)^65 ≤ (319963867281/1000000000000 : ℝ)^49 := by
    have hnat : (4235671249 : ℕ)^65*1000000000000^49 ≤ 319963867281^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235671249 10000000000 319963867281 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1764224889/5000000000 : ℝ)^65 ≤ (25110551278627/100000000000000 : ℝ)^49 := by
    have hnat : (1764224889 : ℕ)^65*100000000000000^49 ≤ 25110551278627^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1764224889 5000000000 25110551278627 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320737169/2500000000 : ℝ)^65 ≤ (10723265493231/25000000000000 : ℝ)^49 := by
    have hnat : (1320737169 : ℕ)^65*25000000000000^49 ≤ 10723265493231^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320737169 2500000000 10723265493231 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4235671249/10000000000 : ℝ), (-1764224889/5000000000 : ℝ), (1320737169/2500000000 : ℝ)] ![(319963867281/1000000000000 : ℝ), (25110551278627/100000000000000 : ℝ), (10723265493231/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4235671249/10000000000 : ℝ)|^65 ≤ (319963867281/1000000000000 : ℝ)^49
        have hw : |(4235671249/10000000000 : ℝ)|=(4235671249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1764224889/5000000000 : ℝ)|^65 ≤ (25110551278627/100000000000000 : ℝ)^49
        have hw : |(-1764224889/5000000000 : ℝ)|=(1764224889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320737169/2500000000 : ℝ)|^65 ≤ (10723265493231/25000000000000 : ℝ)^49
        have hw : |(1320737169/2500000000 : ℝ)|=(1320737169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4235549503/10000000000 : ℝ)*x 0 + (5283032043/10000000000 : ℝ)*x 1 + (-441060487/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4235549503/10000000000 : ℝ)^65 ≤ (15997583379779/50000000000000 : ℝ)^49 := by
    have hnat : (4235549503 : ℕ)^65*50000000000000^49 ≤ 15997583379779^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235549503 10000000000 15997583379779 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5283032043/10000000000 : ℝ)^65 ≤ (8578791972623/20000000000000 : ℝ)^49 := by
    have hnat : (5283032043 : ℕ)^65*20000000000000^49 ≤ 8578791972623^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283032043 10000000000 8578791972623 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441060487/1250000000 : ℝ)^65 ≤ (251108733661/1000000000000 : ℝ)^49 := by
    have hnat : (441060487 : ℕ)^65*1000000000000^49 ≤ 251108733661^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441060487 1250000000 251108733661 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4235549503/10000000000 : ℝ), (5283032043/10000000000 : ℝ), (-441060487/1250000000 : ℝ)] ![(15997583379779/50000000000000 : ℝ), (8578791972623/20000000000000 : ℝ), (251108733661/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4235549503/10000000000 : ℝ)|^65 ≤ (15997583379779/50000000000000 : ℝ)^49
        have hw : |(4235549503/10000000000 : ℝ)|=(4235549503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5283032043/10000000000 : ℝ)|^65 ≤ (8578791972623/20000000000000 : ℝ)^49
        have hw : |(5283032043/10000000000 : ℝ)|=(5283032043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441060487/1250000000 : ℝ)|^65 ≤ (251108733661/1000000000000 : ℝ)^49
        have hw : |(-441060487/1250000000 : ℝ)|=(441060487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301019_s1_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1871980041/5000000000 : ℝ)*x 0 + (4669868943/10000000000 : ℝ)*x 1 + (1167415257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1871980041/5000000000 : ℝ)^65 ≤ (1358253374399/5000000000000 : ℝ)^49 := by
    have hnat : (1871980041 : ℕ)^65*5000000000000^49 ≤ 1358253374399^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871980041 5000000000 1358253374399 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4669868943/10000000000 : ℝ)^65 ≤ (36418541689117/100000000000000 : ℝ)^49 := by
    have hnat : (4669868943 : ℕ)^65*100000000000000^49 ≤ 36418541689117^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4669868943 10000000000 36418541689117 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1167415257/2500000000 : ℝ)^65 ≤ (7283278160219/20000000000000 : ℝ)^49 := by
    have hnat : (1167415257 : ℕ)^65*20000000000000^49 ≤ 7283278160219^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167415257 2500000000 7283278160219 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1871980041/5000000000 : ℝ), (4669868943/10000000000 : ℝ), (1167415257/2500000000 : ℝ)] ![(1358253374399/5000000000000 : ℝ), (36418541689117/100000000000000 : ℝ), (7283278160219/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1871980041/5000000000 : ℝ)|^65 ≤ (1358253374399/5000000000000 : ℝ)^49
        have hw : |(1871980041/5000000000 : ℝ)|=(1871980041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4669868943/10000000000 : ℝ)|^65 ≤ (36418541689117/100000000000000 : ℝ)^49
        have hw : |(4669868943/10000000000 : ℝ)|=(4669868943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1167415257/2500000000 : ℝ)|^65 ≤ (7283278160219/20000000000000 : ℝ)^49
        have hw : |(1167415257/2500000000 : ℝ)|=(1167415257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301019 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-5612564151/10000000000 : ℝ)*X 0 0+(3769915441/10000000000 : ℝ)*X 0 1+(3633393849/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((3805802967/10000000000 : ℝ)*X 1 0+(-36722121/156250000 : ℝ)*X 1 1+(6596955939/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2281093377/5000000000 : ℝ)*X 2 0+(1092896459/2000000000 : ℝ)*X 2 1+(-2953413243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_4 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((533320211/2500000000 : ℝ)*X 0 0+(6837829067/10000000000 : ℝ)*X 0 1+(1848908083/5000000000 : ℝ)*X 0 2+(533320211/2500000000 : ℝ)*X 1 0+(6837829067/10000000000 : ℝ)*X 1 1+(1848908083/5000000000 : ℝ)*X 1 2+(533320211/2500000000 : ℝ)*X 2 0+(6837829067/10000000000 : ℝ)*X 2 1+(1848908083/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-5821852313/10000000000 : ℝ)*X 0 0+(1640028447/5000000000 : ℝ)*X 0 1+(1936562829/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1885513293/5000000000 : ℝ)*X 1 0+(-1801200397/10000000000 : ℝ)*X 1 1+(699816253/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4104674517/10000000000 : ℝ)*X 2 0+(3029083689/5000000000 : ℝ)*X 2 1+(-1365366153/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((396804597/2500000000 : ℝ)*X 0 0+(3884229707/5000000000 : ℝ)*X 0 1+(736378543/2500000000 : ℝ)*X 0 2+(396804597/2500000000 : ℝ)*X 1 0+(3884229707/5000000000 : ℝ)*X 1 1+(736378543/2500000000 : ℝ)*X 1 2+(396804597/2500000000 : ℝ)*X 2 0+(3884229707/5000000000 : ℝ)*X 2 1+(736378543/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-5955517257/10000000000 : ℝ)*X 0 0+(3753829521/10000000000 : ℝ)*X 0 1+(3243493971/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((2037698301/5000000000 : ℝ)*X 1 0+(-2314455049/10000000000 : ℝ)*X 1 1+(1598389061/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4228175011/10000000000 : ℝ)*X 2 0+(5435379141/10000000000 : ℝ)*X 2 1+(-672072949/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((331731731/2000000000 : ℝ)*X 0 0+(1697489157/2500000000 : ℝ)*X 0 1+(412962433/1000000000 : ℝ)*X 0 2+(331731731/2000000000 : ℝ)*X 1 0+(1697489157/2500000000 : ℝ)*X 1 1+(412962433/1000000000 : ℝ)*X 1 2+(331731731/2000000000 : ℝ)*X 2 0+(1697489157/2500000000 : ℝ)*X 2 1+(412962433/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-1134036661/2000000000 : ℝ)*X 0 0+(991275543/2500000000 : ℝ)*X 0 1+(3364362239/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((721327521/2000000000 : ℝ)*X 1 0+(-1085436611/5000000000 : ℝ)*X 1 1+(6886294761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((5095944667/10000000000 : ℝ)*X 2 0+(610488489/1250000000 : ℝ)*X 2 1+(-1511820949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((718012191/5000000000 : ℝ)*X 0 0+(1000322329/1250000000 : ℝ)*X 0 1+(1370928863/5000000000 : ℝ)*X 0 2+(718012191/5000000000 : ℝ)*X 1 0+(1000322329/1250000000 : ℝ)*X 1 1+(1370928863/5000000000 : ℝ)*X 1 2+(718012191/5000000000 : ℝ)*X 2 0+(1000322329/1250000000 : ℝ)*X 2 1+(1370928863/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((567/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(567/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19465256737407527864331/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14441862697/25000000000 : ℝ)*(base49) + (595191676741/500000000000 : ℝ)*(base60) + (3580604851673/500000000000 : ℝ)*(major_s0_0) + (5910000446199/500000000000 : ℝ)*(major_s0_1) + (3580604851673/500000000000 : ℝ)*(major_s0_2) + (16542739/200000000000 : ℝ)*(sp_s0_0) + (4658791189053/1000000000000 : ℝ)*(sp_s0_4) + (592574556327/62500000000 : ℝ)*(sp_s0_7) + (4740558129949/500000000000 : ℝ)*(sp_s0_8) + (474060596559/50000000000 : ℝ)*(sp_s0_9) + (968222091329/200000000000 : ℝ)*(sp_s0_12) + (31841873/500000000000 : ℝ)*(sp_s0_15) + (960617/31250000000 : ℝ)*(sp_s0_19) + (159355029/1000000000000 : ℝ)*(sp_s0_21) + (1210285299097/250000000000 : ℝ)*(f.failure) + (9481275614927/1000000000000 : ℝ)*(f.sum) + (73854173653963/312500000000000000000000000 : ℝ)*base63 + (3926963854644261/5000000000000000000000000000 : ℝ)*base64 + (313351098895957/5000000000000000000000000000 : ℝ)*base66 + (1965737557791597/5000000000000000000000000000 : ℝ)*base69 + (24979582717929/2500000000000000000000000000 : ℝ)*base70 + (484994993355739/5000000000000000000000000000 : ℝ)*base73 + (3595381630671811/5000000000000000000000000000 : ℝ)*base75 + (2331189478291597/5000000000000000000000000000 : ℝ)*base76 + (1476908545270109/2500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (6343/6250000000000000 : ℝ)*base86 + (93/6250000000000000 : ℝ)*base88 + (6343/6250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(6381/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(6381/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1105418381431930470777/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (812067/1000000000000 : ℝ)*(base40) + (1179931539229/1000000000000 : ℝ)*(base49) + (1144013169887/1000000000000 : ℝ)*(base60) + (3559756154881/500000000000 : ℝ)*(major_s0_0) + (3559756154881/500000000000 : ℝ)*(major_s0_1) + (3559756154881/500000000000 : ℝ)*(major_s0_2) + (12590441/250000000000 : ℝ)*(sp_s0_2) + (5391269/1000000000000 : ℝ)*(sp_s0_6) + (6373959/100000000000 : ℝ)*(sp_s0_7) + (1885201319871/200000000000 : ℝ)*(sp_s0_13) + (1885214067789/200000000000 : ℝ)*(sp_s0_14) + (1178250358339/125000000000 : ℝ)*(sp_s0_15) + (4812947415417/1000000000000 : ℝ)*(sp_s0_19) + (17110469/1000000000000 : ℝ)*(sp_s0_22) + (2406476403343/500000000000 : ℝ)*(f.failure) + (1885214067789/200000000000 : ℝ)*(f.sum) + (498330610816309/2500000000000000000000000000 : ℝ)*base63 + (1434278174898483/5000000000000000000000000000 : ℝ)*base65 + (15118926398483/5000000000000000000000000000 : ℝ)*base66 + (1720504146816309/5000000000000000000000000000 : ℝ)*base69 + (142094071208913/2500000000000000000000000000 : ℝ)*base70 + (1383612909898483/5000000000000000000000000000 : ℝ)*base73 + (480423236316309/5000000000000000000000000000 : ℝ)*base75 + (1157605876816309/5000000000000000000000000000 : ℝ)*base76 + (131638899/1000000000000000000000 : ℝ)*base79 + (2483/12500000000000000 : ℝ)*base87 + (2483/12500000000000000 : ℝ)*base89 + (2483/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(16047/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(16047/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2140518480494176999497/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (263563161287/250000000000 : ℝ)*(base49) + (335226231943/1000000000000 : ℝ)*(base60) + (5614937154317/1000000000000 : ℝ)*(major_s0_0) + (6830635192657/1000000000000 : ℝ)*(major_s0_1) + (5614937154317/1000000000000 : ℝ)*(major_s0_2) + (40043333/200000000000 : ℝ)*(sp_s0_1) + (103676357/1000000000000 : ℝ)*(sp_s0_2) + (60784901917/50000000000 : ℝ)*(sp_s0_4) + (239498659/1000000000000 : ℝ)*(sp_s0_12) + (32392093/500000000000 : ℝ)*(sp_s0_13) + (7433981577833/1000000000000 : ℝ)*(sp_s0_20) + (3716923072677/500000000000 : ℝ)*(sp_s0_21) + (3716971342831/500000000000 : ℝ)*(sp_s0_22) + (1897793082367/500000000000 : ℝ)*(sp_s0_25) + (3795825663393/1000000000000 : ℝ)*(f.failure) + (7434046362019/1000000000000 : ℝ)*(f.sum) + (1240412374868357/5000000000000000000000000000 : ℝ)*base62 + (4406834409104169/10000000000000000000000000000 : ℝ)*base64 + (261301703948451/10000000000000000000000000000 : ℝ)*base66 + (2341965935557487/10000000000000000000000000000 : ℝ)*base68 + (2213622124273341/5000000000000000000000000000 : ℝ)*base70 + (1040780574104169/10000000000000000000000000000 : ℝ)*base72 + (702842718179227/10000000000000000000000000000 : ℝ)*base74 + (2445649142442513/10000000000000000000000000000 : ℝ)*base76 + (7704264852631/500000000000000000000000000 : ℝ)*base78 + (11533/25000000000000000 : ℝ)*base87 + (11533/25000000000000000 : ℝ)*base89 + (11533/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (567/2000 : ℝ) ^ (129/32 : ℝ) ≤ (124203699496197269/20000000000000000000 : ℝ) := by
    have hpowers : (567/2000 : ℝ)^129 ≤ (124203699496197269/20000000000000000000 : ℝ)^32 := by
      have hnat : (567 : ℕ)^129*20000000000000000000^32 ≤ 124203699496197269^32*2000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        567 2000 124203699496197269 20000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (567/2000 : ℝ)) (X := (124203699496197269/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (20124203699496197269/20000000000000000000 : ℝ) ≤ (10015369271483429/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (20124203699496197269/20000000000000000000 : ℝ)^32 ≤ (10015369271483429/10000000000000000 : ℝ)^129 := by
      have hnat : (20124203699496197269 : ℕ)^32*10000000000000000^129 ≤ 10015369271483429^129*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20124203699496197269 20000000000000000000 10015369271483429 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015369271483429/10000000000000000 : ℝ)) (X := (20124203699496197269/20000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (10124203699496197269/10000000000000000000 : ℝ) ≤ (10030667381062867/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (10124203699496197269/10000000000000000000 : ℝ)^32 ≤ (10030667381062867/10000000000000000 : ℝ)^129 := by
      have hnat : (10124203699496197269 : ℕ)^32*10000000000000000^129 ≤ 10030667381062867^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10124203699496197269 10000000000000000000 10030667381062867 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030667381062867/10000000000000000 : ℝ)) (X := (10124203699496197269/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(15369271483429/2835000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1092722112817/202500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (567/2000 : ℝ)) (alpha := (15369271483429/2835000000000000 : ℝ)) (beta := (1092722112817/202500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (567/2000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(15369271483429/2835000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1092722112817/202500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (6381/100000 : ℝ) ^ (129/32 : ℝ) ≤ (304255016426717/20000000000000000000 : ℝ) := by
    have hpowers : (6381/100000 : ℝ)^129 ≤ (304255016426717/20000000000000000000 : ℝ)^32 := by
      have hnat : (6381 : ℕ)^129*20000000000000000000^32 ≤ 304255016426717^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6381 100000 304255016426717 20000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6381/100000 : ℝ)) (X := (304255016426717/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (20000304255016426717/20000000000000000000 : ℝ) ≤ (2000007547368093/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (20000304255016426717/20000000000000000000 : ℝ)^32 ≤ (2000007547368093/2000000000000000 : ℝ)^129 := by
      have hnat : (20000304255016426717 : ℕ)^32*2000000000000000^129 ≤ 2000007547368093^129*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20000304255016426717 20000000000000000000 2000007547368093 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000007547368093/2000000000000000 : ℝ)) (X := (20000304255016426717/20000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (10000304255016426717/10000000000000000000 : ℝ) ≤ (5000037736624633/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (10000304255016426717/10000000000000000000 : ℝ)^32 ≤ (5000037736624633/5000000000000000 : ℝ)^129 := by
      have hnat : (10000304255016426717 : ℕ)^32*5000000000000000^129 ≤ 5000037736624633^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000304255016426717 10000000000000000000 5000037736624633 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000037736624633/5000000000000000 : ℝ)) (X := (10000304255016426717/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(7547368093/127620000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(37736408801/638100000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (6381/100000 : ℝ)) (alpha := (7547368093/127620000000000 : ℝ)) (beta := (37736408801/638100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (6381/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(7547368093/127620000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(37736408801/638100000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (16047/100000 : ℝ) ^ (129/32 : ℝ) ≤ (31312228147664111/50000000000000000000 : ℝ) := by
    have hpowers : (16047/100000 : ℝ)^129 ≤ (31312228147664111/50000000000000000000 : ℝ)^32 := by
      have hnat : (16047 : ℕ)^129*50000000000000000000^32 ≤ 31312228147664111^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16047 100000 31312228147664111 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16047/100000 : ℝ)) (X := (31312228147664111/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50031312228147664111/50000000000000000000 : ℝ) ≤ (2500388277313791/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (50031312228147664111/50000000000000000000 : ℝ)^32 ≤ (2500388277313791/2500000000000000 : ℝ)^129 := by
      have hnat : (50031312228147664111 : ℕ)^32*2500000000000000^129 ≤ 2500388277313791^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031312228147664111 50000000000000000000 2500388277313791 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500388277313791/2500000000000000 : ℝ)) (X := (50031312228147664111/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25031312228147664111/25000000000000000000 : ℝ) ≤ (10003105487785331/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (25031312228147664111/25000000000000000000 : ℝ)^32 ≤ (10003105487785331/10000000000000000 : ℝ)^129 := by
      have hnat : (25031312228147664111 : ℕ)^32*10000000000000000^129 ≤ 10003105487785331^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25031312228147664111 25000000000000000000 10003105487785331 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003105487785331/10000000000000000 : ℝ)) (X := (25031312228147664111/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(388277313791/401175000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1552378530167/1604700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (16047/100000 : ℝ)) (alpha := (388277313791/401175000000000 : ℝ)) (beta := (1552378530167/1604700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (16047/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(388277313791/401175000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1552378530167/1604700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2454658369/5000000000 : ℝ)*X 0 0+(4089618041/10000000000 : ℝ)*X 0 1+(2044887569/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4235671249/10000000000 : ℝ)*X 1 0+(-1764224889/5000000000 : ℝ)*X 1 1+(1320737169/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4235549503/10000000000 : ℝ)*X 2 0+(5283032043/10000000000 : ℝ)*X 2 1+(-441060487/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1871980041/5000000000 : ℝ)*X 0 0+(4669868943/10000000000 : ℝ)*X 0 1+(1167415257/2500000000 : ℝ)*X 0 2+(1871980041/5000000000 : ℝ)*X 1 0+(4669868943/10000000000 : ℝ)*X 1 1+(1167415257/2500000000 : ℝ)*X 1 2+(1871980041/5000000000 : ℝ)*X 2 0+(4669868943/10000000000 : ℝ)*X 2 1+(1167415257/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301019_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-73443/12500 : ℝ) < ((-36981/25000 : ℝ)*P 0+(-36981/25000 : ℝ)*P 1+(-36981/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-73443/12500 : ℝ) < (-247186991046309615897920551828697/42664961250000000000000000000000 : ℝ) := by norm_num
    linear_combination (189291/1000000000000 : ℝ)*(base1) + (103703/500000000000 : ℝ)*(base15) + (216397/1000000000000 : ℝ)*(base33) + (129581/1000000000000 : ℝ)*(base39) + (254567455117/500000000000 : ℝ)*(base49) + (286776310509/1000000000000 : ℝ)*(base50) + (30760920457/500000000000 : ℝ)*(base59) + (4459507463/15625000000 : ℝ)*(base60) + (1479239783603/1000000000000 : ℝ)*(major_s1_0) + (36981/25000 : ℝ)*(major_s1_1) + (36981/25000 : ℝ)*(major_s1_2) + (965612874639/500000000000 : ℝ)*(sp_s1_0) + (1931225136183/1000000000000 : ℝ)*(sp_s1_1) + (193122534359/100000000000 : ℝ)*(sp_s1_2) + (999999810709/1000000000000 : ℝ)*(sp_s1_6) + (1931225559987/1000000000000 : ℝ)*(f.sum) + (1187293957663411/6320735000000000000000000000 : ℝ)*base63 + (1688189884349/3566000000000000000000000 : ℝ)*base65 + (263162672241/443125000000000000000000 : ℝ)*base67 + (4083646136597/3566000000000000000000000 : ℝ)*base69 + (2091564844615540421/5054805000000000000000000000000 : ℝ)*base71 + (149480708399651/202500000000000000000000000 : ℝ)*base73 + (217383644807/1772500000000000000000000 : ℝ)*base75 + (18869404894813/2835000000000000000000000000 : ℝ)*base76 + (163415997684175559/143572500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p001_b009 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 19 ≤ c.val) (hhi : c.val < 20)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=19 := by omega
  rcases hc with rfl
  · exact collision_c301019 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 19 ≤ c.val) (hhi : c.val < 20)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b009 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

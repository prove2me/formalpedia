-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b106
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:34:02.114141+00:00
-- url     : https://prove2.me/submissions/dfbf94eb-611e-437d-82a5-e3488638dfbf

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
theorem collision_support_c201273_s0_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (44806091/10000000000 : ℝ)*x 0 + (-8774962467/10000000000 : ℝ)*x 1 + (-2418170293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44806091/10000000000 : ℝ)^17 ≤ (8485384679/10000000000000 : ℝ)^13 := by
    have hnat : (44806091 : ℕ)^17*10000000000000^13 ≤ 8485384679^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44806091 10000000000 8485384679 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8774962467/10000000000 : ℝ)^17 ≤ (42145603521199/50000000000000 : ℝ)^13 := by
    have hnat : (8774962467 : ℕ)^17*50000000000000^13 ≤ 42145603521199^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8774962467 10000000000 42145603521199 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2418170293/10000000000 : ℝ)^17 ≤ (15623939100423/100000000000000 : ℝ)^13 := by
    have hnat : (2418170293 : ℕ)^17*100000000000000^13 ≤ 15623939100423^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418170293 10000000000 15623939100423 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44806091/10000000000 : ℝ), (-8774962467/10000000000 : ℝ), (-2418170293/10000000000 : ℝ)] ![(8485384679/10000000000000 : ℝ), (42145603521199/50000000000000 : ℝ), (15623939100423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44806091/10000000000 : ℝ)|^17 ≤ (8485384679/10000000000000 : ℝ)^13
        have hw : |(44806091/10000000000 : ℝ)|=(44806091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8774962467/10000000000 : ℝ)|^17 ≤ (42145603521199/50000000000000 : ℝ)^13
        have hw : |(-8774962467/10000000000 : ℝ)|=(8774962467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2418170293/10000000000 : ℝ)|^17 ≤ (15623939100423/100000000000000 : ℝ)^13
        have hw : |(-2418170293/10000000000 : ℝ)|=(2418170293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s0_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (140105523/156250000 : ℝ)*x 0 + (362805627/10000000000 : ℝ)*x 1 + (987115557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140105523/156250000 : ℝ)^17 ≤ (43354228121901/50000000000000 : ℝ)^13 := by
    have hnat : (140105523 : ℕ)^17*50000000000000^13 ≤ 43354228121901^13*156250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140105523 156250000 43354228121901 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (362805627/10000000000 : ℝ)^17 ≤ (1307665866951/100000000000000 : ℝ)^13 := by
    have hnat : (362805627 : ℕ)^17*100000000000000^13 ≤ 1307665866951^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362805627 10000000000 1307665866951 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (987115557/5000000000 : ℝ)^17 ≤ (2396775573603/20000000000000 : ℝ)^13 := by
    have hnat : (987115557 : ℕ)^17*20000000000000^13 ≤ 2396775573603^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987115557 5000000000 2396775573603 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(140105523/156250000 : ℝ), (362805627/10000000000 : ℝ), (987115557/5000000000 : ℝ)] ![(43354228121901/50000000000000 : ℝ), (1307665866951/100000000000000 : ℝ), (2396775573603/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(140105523/156250000 : ℝ)|^17 ≤ (43354228121901/50000000000000 : ℝ)^13
        have hw : |(140105523/156250000 : ℝ)|=(140105523/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(362805627/10000000000 : ℝ)|^17 ≤ (1307665866951/100000000000000 : ℝ)^13
        have hw : |(362805627/10000000000 : ℝ)|=(362805627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(987115557/5000000000 : ℝ)|^17 ≤ (2396775573603/20000000000000 : ℝ)^13
        have hw : |(987115557/5000000000 : ℝ)|=(987115557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s0_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (9322046537/10000000000 : ℝ)*x 0 + (-356473979/10000000000 : ℝ)*x 1 + (689355033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9322046537/10000000000 : ℝ)^17 ≤ (45614206285281/50000000000000 : ℝ)^13 := by
    have hnat : (9322046537 : ℕ)^17*50000000000000^13 ≤ 45614206285281^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9322046537 10000000000 45614206285281 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (356473979/10000000000 : ℝ)^17 ≤ (1277903137757/100000000000000 : ℝ)^13 := by
    have hnat : (356473979 : ℕ)^17*100000000000000^13 ≤ 1277903137757^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356473979 10000000000 1277903137757 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (689355033/5000000000 : ℝ)^17 ≤ (7493684275991/100000000000000 : ℝ)^13 := by
    have hnat : (689355033 : ℕ)^17*100000000000000^13 ≤ 7493684275991^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689355033 5000000000 7493684275991 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9322046537/10000000000 : ℝ), (-356473979/10000000000 : ℝ), (689355033/5000000000 : ℝ)] ![(45614206285281/50000000000000 : ℝ), (1277903137757/100000000000000 : ℝ), (7493684275991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9322046537/10000000000 : ℝ)|^17 ≤ (45614206285281/50000000000000 : ℝ)^13
        have hw : |(9322046537/10000000000 : ℝ)|=(9322046537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-356473979/10000000000 : ℝ)|^17 ≤ (1277903137757/100000000000000 : ℝ)^13
        have hw : |(-356473979/10000000000 : ℝ)|=(356473979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(689355033/5000000000 : ℝ)|^17 ≤ (7493684275991/100000000000000 : ℝ)^13
        have hw : |(689355033/5000000000 : ℝ)|=(689355033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s0_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7878247/312500000 : ℝ)*x 0 + (-9931351157/10000000000 : ℝ)*x 1 + (-44618061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7878247/312500000 : ℝ)^17 ≤ (812377526497/100000000000000 : ℝ)^13 := by
    have hnat : (7878247 : ℕ)^17*100000000000000^13 ≤ 812377526497^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7878247 312500000 812377526497 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9931351157/10000000000 : ℝ)^17 ≤ (49551616988497/50000000000000 : ℝ)^13 := by
    have hnat : (9931351157 : ℕ)^17*50000000000000^13 ≤ 49551616988497^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9931351157 10000000000 49551616988497 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44618061/10000000000 : ℝ)^17 ≤ (16877697917/20000000000000 : ℝ)^13 := by
    have hnat : (44618061 : ℕ)^17*20000000000000^13 ≤ 16877697917^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44618061 10000000000 16877697917 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7878247/312500000 : ℝ), (-9931351157/10000000000 : ℝ), (-44618061/10000000000 : ℝ)] ![(812377526497/100000000000000 : ℝ), (49551616988497/50000000000000 : ℝ), (16877697917/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7878247/312500000 : ℝ)|^17 ≤ (812377526497/100000000000000 : ℝ)^13
        have hw : |(7878247/312500000 : ℝ)|=(7878247/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9931351157/10000000000 : ℝ)|^17 ≤ (49551616988497/50000000000000 : ℝ)^13
        have hw : |(-9931351157/10000000000 : ℝ)|=(9931351157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44618061/10000000000 : ℝ)|^17 ≤ (16877697917/20000000000000 : ℝ)^13
        have hw : |(-44618061/10000000000 : ℝ)|=(44618061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s0_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1046299/10000000000 : ℝ)*x 0 + (-1022870731/5000000000 : ℝ)*x 1 + (902491947/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046299/10000000000 : ℝ)^17 ≤ (311820401/50000000000000 : ℝ)^13 := by
    have hnat : (1046299 : ℕ)^17*50000000000000^13 ≤ 311820401^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046299 10000000000 311820401 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1022870731/5000000000 : ℝ)^17 ≤ (12554656171631/100000000000000 : ℝ)^13 := by
    have hnat : (1022870731 : ℕ)^17*100000000000000^13 ≤ 12554656171631^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022870731 5000000000 12554656171631 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902491947/1000000000 : ℝ)^17 ≤ (87444720184641/100000000000000 : ℝ)^13 := by
    have hnat : (902491947 : ℕ)^17*100000000000000^13 ≤ 87444720184641^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902491947 1000000000 87444720184641 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1046299/10000000000 : ℝ), (-1022870731/5000000000 : ℝ), (902491947/1000000000 : ℝ)] ![(311820401/50000000000000 : ℝ), (12554656171631/100000000000000 : ℝ), (87444720184641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1046299/10000000000 : ℝ)|^17 ≤ (311820401/50000000000000 : ℝ)^13
        have hw : |(-1046299/10000000000 : ℝ)|=(1046299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1022870731/5000000000 : ℝ)|^17 ≤ (12554656171631/100000000000000 : ℝ)^13
        have hw : |(-1022870731/5000000000 : ℝ)|=(1022870731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902491947/1000000000 : ℝ)|^17 ≤ (87444720184641/100000000000000 : ℝ)^13
        have hw : |(902491947/1000000000 : ℝ)|=(902491947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s0_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8070991243/10000000000 : ℝ)*x 0 + (586959129/10000000000 : ℝ)*x 1 + (98131063/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8070991243/10000000000 : ℝ)^17 ≤ (9444935682381/12500000000000 : ℝ)^13 := by
    have hnat : (8070991243 : ℕ)^17*12500000000000^13 ≤ 9444935682381^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8070991243 10000000000 9444935682381 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (586959129/10000000000 : ℝ)^17 ≤ (2453115366161/100000000000000 : ℝ)^13 := by
    have hnat : (586959129 : ℕ)^17*100000000000000^13 ≤ 2453115366161^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586959129 10000000000 2453115366161 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (98131063/312500000 : ℝ)^17 ≤ (5496849789447/25000000000000 : ℝ)^13 := by
    have hnat : (98131063 : ℕ)^17*25000000000000^13 ≤ 5496849789447^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98131063 312500000 5496849789447 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8070991243/10000000000 : ℝ), (586959129/10000000000 : ℝ), (98131063/312500000 : ℝ)] ![(9444935682381/12500000000000 : ℝ), (2453115366161/100000000000000 : ℝ), (5496849789447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8070991243/10000000000 : ℝ)|^17 ≤ (9444935682381/12500000000000 : ℝ)^13
        have hw : |(8070991243/10000000000 : ℝ)|=(8070991243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(586959129/10000000000 : ℝ)|^17 ≤ (2453115366161/100000000000000 : ℝ)^13
        have hw : |(586959129/10000000000 : ℝ)|=(586959129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(98131063/312500000 : ℝ)|^17 ≤ (5496849789447/25000000000000 : ℝ)^13
        have hw : |(98131063/312500000 : ℝ)|=(98131063/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s0_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (925705927/1000000000 : ℝ)*x 0 + (-494410389/10000000000 : ℝ)*x 1 + (349893117/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (925705927/1000000000 : ℝ)^17 ≤ (5649852051101/6250000000000 : ℝ)^13 := by
    have hnat : (925705927 : ℕ)^17*6250000000000^13 ≤ 5649852051101^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925705927 1000000000 5649852051101 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (494410389/10000000000 : ℝ)^17 ≤ (980027784881/50000000000000 : ℝ)^13 := by
    have hnat : (494410389 : ℕ)^17*50000000000000^13 ≤ 980027784881^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494410389 10000000000 980027784881 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (349893117/2500000000 : ℝ)^17 ≤ (955288950697/12500000000000 : ℝ)^13 := by
    have hnat : (349893117 : ℕ)^17*12500000000000^13 ≤ 955288950697^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349893117 2500000000 955288950697 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(925705927/1000000000 : ℝ), (-494410389/10000000000 : ℝ), (349893117/2500000000 : ℝ)] ![(5649852051101/6250000000000 : ℝ), (980027784881/50000000000000 : ℝ), (955288950697/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(925705927/1000000000 : ℝ)|^17 ≤ (5649852051101/6250000000000 : ℝ)^13
        have hw : |(925705927/1000000000 : ℝ)|=(925705927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-494410389/10000000000 : ℝ)|^17 ≤ (980027784881/50000000000000 : ℝ)^13
        have hw : |(-494410389/10000000000 : ℝ)|=(494410389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(349893117/2500000000 : ℝ)|^17 ≤ (955288950697/12500000000000 : ℝ)^13
        have hw : |(349893117/2500000000 : ℝ)|=(349893117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s0_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4097171/10000000000 : ℝ)*x 0 + (-9996750179/10000000000 : ℝ)*x 1 + (12309693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4097171/10000000000 : ℝ)^17 ≤ (371681977/10000000000000 : ℝ)^13 := by
    have hnat : (4097171 : ℕ)^17*10000000000000^13 ≤ 371681977^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4097171 10000000000 371681977 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9996750179/10000000000 : ℝ)^17 ≤ (19991500893139/20000000000000 : ℝ)^13 := by
    have hnat : (9996750179 : ℕ)^17*20000000000000^13 ≤ 19991500893139^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9996750179 10000000000 19991500893139 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12309693/5000000000 : ℝ)^17 ≤ (4847337931/12500000000000 : ℝ)^13 := by
    have hnat : (12309693 : ℕ)^17*12500000000000^13 ≤ 4847337931^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12309693 5000000000 4847337931 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4097171/10000000000 : ℝ), (-9996750179/10000000000 : ℝ), (12309693/5000000000 : ℝ)] ![(371681977/10000000000000 : ℝ), (19991500893139/20000000000000 : ℝ), (4847337931/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4097171/10000000000 : ℝ)|^17 ≤ (371681977/10000000000000 : ℝ)^13
        have hw : |(4097171/10000000000 : ℝ)|=(4097171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9996750179/10000000000 : ℝ)|^17 ≤ (19991500893139/20000000000000 : ℝ)^13
        have hw : |(-9996750179/10000000000 : ℝ)|=(9996750179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12309693/5000000000 : ℝ)|^17 ≤ (4847337931/12500000000000 : ℝ)^13
        have hw : |(12309693/5000000000 : ℝ)|=(12309693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s0_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (71238311/5000000000 : ℝ)*x 0 + (-3100204193/5000000000 : ℝ)*x 1 + (-5530482681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71238311/5000000000 : ℝ)^17 ≤ (192590439779/50000000000000 : ℝ)^13 := by
    have hnat : (71238311 : ℕ)^17*50000000000000^13 ≤ 192590439779^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71238311 5000000000 192590439779 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3100204193/5000000000 : ℝ)^17 ≤ (26762064978721/50000000000000 : ℝ)^13 := by
    have hnat : (3100204193 : ℕ)^17*50000000000000^13 ≤ 26762064978721^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3100204193 5000000000 26762064978721 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5530482681/10000000000 : ℝ)^17 ≤ (2880668071921/6250000000000 : ℝ)^13 := by
    have hnat : (5530482681 : ℕ)^17*6250000000000^13 ≤ 2880668071921^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5530482681 10000000000 2880668071921 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(71238311/5000000000 : ℝ), (-3100204193/5000000000 : ℝ), (-5530482681/10000000000 : ℝ)] ![(192590439779/50000000000000 : ℝ), (26762064978721/50000000000000 : ℝ), (2880668071921/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(71238311/5000000000 : ℝ)|^17 ≤ (192590439779/50000000000000 : ℝ)^13
        have hw : |(71238311/5000000000 : ℝ)|=(71238311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3100204193/5000000000 : ℝ)|^17 ≤ (26762064978721/50000000000000 : ℝ)^13
        have hw : |(-3100204193/5000000000 : ℝ)|=(3100204193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5530482681/10000000000 : ℝ)|^17 ≤ (2880668071921/6250000000000 : ℝ)^13
        have hw : |(-5530482681/10000000000 : ℝ)|=(5530482681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s0_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8491587357/10000000000 : ℝ)*x 0 + (244964101/10000000000 : ℝ)*x 1 + (2748084787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8491587357/10000000000 : ℝ)^17 ≤ (8074940053513/10000000000000 : ℝ)^13 := by
    have hnat : (8491587357 : ℕ)^17*10000000000000^13 ≤ 8074940053513^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8491587357 10000000000 8074940053513 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244964101/10000000000 : ℝ)^17 ≤ (782423088567/100000000000000 : ℝ)^13 := by
    have hnat : (244964101 : ℕ)^17*100000000000000^13 ≤ 782423088567^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244964101 10000000000 782423088567 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2748084787/10000000000 : ℝ)^17 ≤ (4617044093229/25000000000000 : ℝ)^13 := by
    have hnat : (2748084787 : ℕ)^17*25000000000000^13 ≤ 4617044093229^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748084787 10000000000 4617044093229 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8491587357/10000000000 : ℝ), (244964101/10000000000 : ℝ), (2748084787/10000000000 : ℝ)] ![(8074940053513/10000000000000 : ℝ), (782423088567/100000000000000 : ℝ), (4617044093229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8491587357/10000000000 : ℝ)|^17 ≤ (8074940053513/10000000000000 : ℝ)^13
        have hw : |(8491587357/10000000000 : ℝ)|=(8491587357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(244964101/10000000000 : ℝ)|^17 ≤ (782423088567/100000000000000 : ℝ)^13
        have hw : |(244964101/10000000000 : ℝ)|=(244964101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2748084787/10000000000 : ℝ)|^17 ≤ (4617044093229/25000000000000 : ℝ)^13
        have hw : |(2748084787/10000000000 : ℝ)|=(2748084787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s0_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (553150851/625000000 : ℝ)*x 0 + (-35156053/1000000000 : ℝ)*x 1 + (1081558951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (553150851/625000000 : ℝ)^17 ≤ (85240240274409/100000000000000 : ℝ)^13 := by
    have hnat : (553150851 : ℕ)^17*100000000000000^13 ≤ 85240240274409^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553150851 625000000 85240240274409 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35156053/1000000000 : ℝ)^17 ≤ (1254918521491/100000000000000 : ℝ)^13 := by
    have hnat : (35156053 : ℕ)^17*100000000000000^13 ≤ 1254918521491^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35156053 1000000000 1254918521491 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081558951/5000000000 : ℝ)^17 ≤ (1688105147951/12500000000000 : ℝ)^13 := by
    have hnat : (1081558951 : ℕ)^17*12500000000000^13 ≤ 1688105147951^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081558951 5000000000 1688105147951 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(553150851/625000000 : ℝ), (-35156053/1000000000 : ℝ), (1081558951/5000000000 : ℝ)] ![(85240240274409/100000000000000 : ℝ), (1254918521491/100000000000000 : ℝ), (1688105147951/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(553150851/625000000 : ℝ)|^17 ≤ (85240240274409/100000000000000 : ℝ)^13
        have hw : |(553150851/625000000 : ℝ)|=(553150851/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35156053/1000000000 : ℝ)|^17 ≤ (1254918521491/100000000000000 : ℝ)^13
        have hw : |(-35156053/1000000000 : ℝ)|=(35156053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081558951/5000000000 : ℝ)|^17 ≤ (1688105147951/12500000000000 : ℝ)^13
        have hw : |(1081558951/5000000000 : ℝ)|=(1081558951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s0_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (13515039/500000000 : ℝ)*x 0 + (-9930475463/10000000000 : ℝ)*x 1 + (3465593/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13515039/500000000 : ℝ)^17 ≤ (889895018227/100000000000000 : ℝ)^13 := by
    have hnat : (13515039 : ℕ)^17*100000000000000^13 ≤ 889895018227^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13515039 500000000 889895018227 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9930475463/10000000000 : ℝ)^17 ≤ (774154742149/781250000000 : ℝ)^13 := by
    have hnat : (9930475463 : ℕ)^17*781250000000^13 ≤ 774154742149^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9930475463 10000000000 774154742149 781250000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3465593/2500000000 : ℝ)^17 ≤ (18297971583/100000000000000 : ℝ)^13 := by
    have hnat : (3465593 : ℕ)^17*100000000000000^13 ≤ 18297971583^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3465593 2500000000 18297971583 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13515039/500000000 : ℝ), (-9930475463/10000000000 : ℝ), (3465593/2500000000 : ℝ)] ![(889895018227/100000000000000 : ℝ), (774154742149/781250000000 : ℝ), (18297971583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13515039/500000000 : ℝ)|^17 ≤ (889895018227/100000000000000 : ℝ)^13
        have hw : |(13515039/500000000 : ℝ)|=(13515039/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9930475463/10000000000 : ℝ)|^17 ≤ (774154742149/781250000000 : ℝ)^13
        have hw : |(-9930475463/10000000000 : ℝ)|=(9930475463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3465593/2500000000 : ℝ)|^17 ≤ (18297971583/100000000000000 : ℝ)^13
        have hw : |(3465593/2500000000 : ℝ)|=(3465593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s0_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (148927047/5000000000 : ℝ)*x 0 + (-216686251/2000000000 : ℝ)*x 1 + (-950072859/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (148927047/5000000000 : ℝ)^17 ≤ (101033689341/10000000000000 : ℝ)^13 := by
    have hnat : (148927047 : ℕ)^17*10000000000000^13 ≤ 101033689341^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148927047 5000000000 101033689341 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216686251/2000000000 : ℝ)^17 ≤ (5467857190187/100000000000000 : ℝ)^13 := by
    have hnat : (216686251 : ℕ)^17*100000000000000^13 ≤ 5467857190187^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216686251 2000000000 5467857190187 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (950072859/1000000000 : ℝ)^17 ≤ (5845112869283/6250000000000 : ℝ)^13 := by
    have hnat : (950072859 : ℕ)^17*6250000000000^13 ≤ 5845112869283^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950072859 1000000000 5845112869283 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(148927047/5000000000 : ℝ), (-216686251/2000000000 : ℝ), (-950072859/1000000000 : ℝ)] ![(101033689341/10000000000000 : ℝ), (5467857190187/100000000000000 : ℝ), (5845112869283/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(148927047/5000000000 : ℝ)|^17 ≤ (101033689341/10000000000000 : ℝ)^13
        have hw : |(148927047/5000000000 : ℝ)|=(148927047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216686251/2000000000 : ℝ)|^17 ≤ (5467857190187/100000000000000 : ℝ)^13
        have hw : |(-216686251/2000000000 : ℝ)|=(216686251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-950072859/1000000000 : ℝ)|^17 ≤ (5845112869283/6250000000000 : ℝ)^13
        have hw : |(-950072859/1000000000 : ℝ)|=(950072859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s0_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4164914519/5000000000 : ℝ)*x 0 + (59927487/625000000 : ℝ)*x 1 + (2532356467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4164914519/5000000000 : ℝ)^17 ≤ (78743809743303/100000000000000 : ℝ)^13 := by
    have hnat : (4164914519 : ℕ)^17*100000000000000^13 ≤ 78743809743303^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164914519 5000000000 78743809743303 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (59927487/625000000 : ℝ)^17 ≤ (2330274835991/50000000000000 : ℝ)^13 := by
    have hnat : (59927487 : ℕ)^17*50000000000000^13 ≤ 2330274835991^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59927487 625000000 2330274835991 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2532356467/10000000000 : ℝ)^17 ≤ (16595640572833/100000000000000 : ℝ)^13 := by
    have hnat : (2532356467 : ℕ)^17*100000000000000^13 ≤ 16595640572833^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2532356467 10000000000 16595640572833 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4164914519/5000000000 : ℝ), (59927487/625000000 : ℝ), (2532356467/10000000000 : ℝ)] ![(78743809743303/100000000000000 : ℝ), (2330274835991/50000000000000 : ℝ), (16595640572833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4164914519/5000000000 : ℝ)|^17 ≤ (78743809743303/100000000000000 : ℝ)^13
        have hw : |(4164914519/5000000000 : ℝ)|=(4164914519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(59927487/625000000 : ℝ)|^17 ≤ (2330274835991/50000000000000 : ℝ)^13
        have hw : |(59927487/625000000 : ℝ)|=(59927487/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2532356467/10000000000 : ℝ)|^17 ≤ (16595640572833/100000000000000 : ℝ)^13
        have hw : |(2532356467/10000000000 : ℝ)|=(2532356467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s0_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4695051171/5000000000 : ℝ)*x 0 + (-149588563/2000000000 : ℝ)*x 1 + (469251769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4695051171/5000000000 : ℝ)^17 ≤ (23025082964519/25000000000000 : ℝ)^13 := by
    have hnat : (4695051171 : ℕ)^17*25000000000000^13 ≤ 23025082964519^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4695051171 5000000000 23025082964519 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149588563/2000000000 : ℝ)^17 ≤ (3367955635469/100000000000000 : ℝ)^13 := by
    have hnat : (149588563 : ℕ)^17*100000000000000^13 ≤ 3367955635469^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149588563 2000000000 3367955635469 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (469251769/5000000000 : ℝ)^17 ≤ (453171249653/10000000000000 : ℝ)^13 := by
    have hnat : (469251769 : ℕ)^17*10000000000000^13 ≤ 453171249653^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469251769 5000000000 453171249653 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4695051171/5000000000 : ℝ), (-149588563/2000000000 : ℝ), (469251769/5000000000 : ℝ)] ![(23025082964519/25000000000000 : ℝ), (3367955635469/100000000000000 : ℝ), (453171249653/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4695051171/5000000000 : ℝ)|^17 ≤ (23025082964519/25000000000000 : ℝ)^13
        have hw : |(4695051171/5000000000 : ℝ)|=(4695051171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-149588563/2000000000 : ℝ)|^17 ≤ (3367955635469/100000000000000 : ℝ)^13
        have hw : |(-149588563/2000000000 : ℝ)|=(149588563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(469251769/5000000000 : ℝ)|^17 ≤ (453171249653/10000000000000 : ℝ)^13
        have hw : |(469251769/5000000000 : ℝ)|=(469251769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s1_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4079717/5000000000 : ℝ)*x 0 + (-9997848003/10000000000 : ℝ)*x 1 + (-7131043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4079717/5000000000 : ℝ)^17 ≤ (2287397233/25000000000000 : ℝ)^13 := by
    have hnat : (4079717 : ℕ)^17*25000000000000^13 ≤ 2287397233^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4079717 5000000000 2287397233 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9997848003/10000000000 : ℝ)^17 ≤ (19994371886503/20000000000000 : ℝ)^13 := by
    have hnat : (9997848003 : ℕ)^17*20000000000000^13 ≤ 19994371886503^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9997848003 10000000000 19994371886503 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7131043/5000000000 : ℝ)^17 ≤ (4747741613/25000000000000 : ℝ)^13 := by
    have hnat : (7131043 : ℕ)^17*25000000000000^13 ≤ 4747741613^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7131043 5000000000 4747741613 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4079717/5000000000 : ℝ), (-9997848003/10000000000 : ℝ), (-7131043/5000000000 : ℝ)] ![(2287397233/25000000000000 : ℝ), (19994371886503/20000000000000 : ℝ), (4747741613/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4079717/5000000000 : ℝ)|^17 ≤ (2287397233/25000000000000 : ℝ)^13
        have hw : |(4079717/5000000000 : ℝ)|=(4079717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9997848003/10000000000 : ℝ)|^17 ≤ (19994371886503/20000000000000 : ℝ)^13
        have hw : |(-9997848003/10000000000 : ℝ)|=(9997848003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7131043/5000000000 : ℝ)|^17 ≤ (4747741613/25000000000000 : ℝ)^13
        have hw : |(-7131043/5000000000 : ℝ)|=(7131043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s1_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-23948723/1250000000 : ℝ)*x 0 + (-2406834751/2500000000 : ℝ)*x 1 + (449002113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23948723/1250000000 : ℝ)^17 ≤ (141844186343/25000000000000 : ℝ)^13 := by
    have hnat : (23948723 : ℕ)^17*25000000000000^13 ≤ 141844186343^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23948723 1250000000 141844186343 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2406834751/2500000000 : ℝ)^17 ≤ (95154924558647/100000000000000 : ℝ)^13 := by
    have hnat : (2406834751 : ℕ)^17*100000000000000^13 ≤ 95154924558647^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406834751 2500000000 95154924558647 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449002113/5000000000 : ℝ)^17 ≤ (171107947243/4000000000000 : ℝ)^13 := by
    have hnat : (449002113 : ℕ)^17*4000000000000^13 ≤ 171107947243^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449002113 5000000000 171107947243 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23948723/1250000000 : ℝ), (-2406834751/2500000000 : ℝ), (449002113/5000000000 : ℝ)] ![(141844186343/25000000000000 : ℝ), (95154924558647/100000000000000 : ℝ), (171107947243/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23948723/1250000000 : ℝ)|^17 ≤ (141844186343/25000000000000 : ℝ)^13
        have hw : |(-23948723/1250000000 : ℝ)|=(23948723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2406834751/2500000000 : ℝ)|^17 ≤ (95154924558647/100000000000000 : ℝ)^13
        have hw : |(-2406834751/2500000000 : ℝ)|=(2406834751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449002113/5000000000 : ℝ)|^17 ≤ (171107947243/4000000000000 : ℝ)^13
        have hw : |(449002113/5000000000 : ℝ)|=(449002113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s1_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (9345662957/10000000000 : ℝ)*x 0 + (386299143/10000000000 : ℝ)*x 1 + (1315805869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9345662957/10000000000 : ℝ)^17 ≤ (45765380466217/50000000000000 : ℝ)^13 := by
    have hnat : (9345662957 : ℕ)^17*50000000000000^13 ≤ 45765380466217^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9345662957 10000000000 45765380466217 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386299143/10000000000 : ℝ)^17 ≤ (22179465541/1562500000000 : ℝ)^13 := by
    have hnat : (386299143 : ℕ)^17*1562500000000^13 ≤ 22179465541^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386299143 10000000000 22179465541 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315805869/10000000000 : ℝ)^17 ≤ (7049753265881/100000000000000 : ℝ)^13 := by
    have hnat : (1315805869 : ℕ)^17*100000000000000^13 ≤ 7049753265881^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315805869 10000000000 7049753265881 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9345662957/10000000000 : ℝ), (386299143/10000000000 : ℝ), (1315805869/10000000000 : ℝ)] ![(45765380466217/50000000000000 : ℝ), (22179465541/1562500000000 : ℝ), (7049753265881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9345662957/10000000000 : ℝ)|^17 ≤ (45765380466217/50000000000000 : ℝ)^13
        have hw : |(9345662957/10000000000 : ℝ)|=(9345662957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(386299143/10000000000 : ℝ)|^17 ≤ (22179465541/1562500000000 : ℝ)^13
        have hw : |(386299143/10000000000 : ℝ)|=(386299143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315805869/10000000000 : ℝ)|^17 ≤ (7049753265881/100000000000000 : ℝ)^13
        have hw : |(1315805869/10000000000 : ℝ)|=(1315805869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c201273_s1_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4823907063/5000000000 : ℝ)*x 0 + (-19249409/1250000000 : ℝ)*x 1 + (439034883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4823907063/5000000000 : ℝ)^17 ≤ (95419652070591/100000000000000 : ℝ)^13 := by
    have hnat : (4823907063 : ℕ)^17*100000000000000^13 ≤ 95419652070591^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4823907063 5000000000 95419652070591 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19249409/1250000000 : ℝ)^17 ≤ (85280030733/20000000000000 : ℝ)^13 := by
    have hnat : (19249409 : ℕ)^17*20000000000000^13 ≤ 85280030733^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19249409 1250000000 85280030733 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439034883/5000000000 : ℝ)^17 ≤ (4153947763397/100000000000000 : ℝ)^13 := by
    have hnat : (439034883 : ℕ)^17*100000000000000^13 ≤ 4153947763397^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439034883 5000000000 4153947763397 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4823907063/5000000000 : ℝ), (-19249409/1250000000 : ℝ), (439034883/5000000000 : ℝ)] ![(95419652070591/100000000000000 : ℝ), (85280030733/20000000000000 : ℝ), (4153947763397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4823907063/5000000000 : ℝ)|^17 ≤ (95419652070591/100000000000000 : ℝ)^13
        have hw : |(4823907063/5000000000 : ℝ)|=(4823907063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19249409/1250000000 : ℝ)|^17 ≤ (85280030733/20000000000000 : ℝ)^13
        have hw : |(-19249409/1250000000 : ℝ)|=(19249409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(439034883/5000000000 : ℝ)|^17 ≤ (4153947763397/100000000000000 : ℝ)^13
        have hw : |(439034883/5000000000 : ℝ)|=(439034883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c201273 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 2, 1], ![0, 2, 1], ![1, 0, 2]] ![![true, true, true], ![true, false, true], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) ∧ ((-1 : ℝ)*(X 0 1+X 2 1)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 1) ∧ ((-1 : ℝ)*pair X 1 1) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) ∧ ((-1 : ℝ)*(X 0 2+X 1 2)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 2) ∧ ((-1 : ℝ)*pair X 2 2) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*X 1 2+(1 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 2) ≤ (0 : ℝ) := by
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
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2))+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 2, 1], ![0, 2, 1], ![1, 0, 2]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2)+(12218720220587/100000000000000 : ℝ)*((1 : ℝ)*pair X 0 1) at hh
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 0+X 2 0))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 2, 1], ![0, 2, 1], ![1, 0, 2]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 0)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*pair X 1 1) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 1+X 1 1))+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (365957637479293/2000000000000000 : ℝ)) (beta := (12218720220587/100000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 2, 1], ![0, 2, 1], ![1, 0, 2]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 1)+(365957637479293/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(12218720220587/100000000000000 : ℝ)*((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((44806091/10000000000 : ℝ)*X 1 0+(-8774962467/10000000000 : ℝ)*X 1 1+(-2418170293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((140105523/156250000 : ℝ)*X 2 0+(362805627/10000000000 : ℝ)*X 2 1+(987115557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((9322046537/10000000000 : ℝ)*X 0 0+(-356473979/10000000000 : ℝ)*X 0 1+(689355033/5000000000 : ℝ)*X 0 2+(9322046537/10000000000 : ℝ)*X 1 0+(-356473979/10000000000 : ℝ)*X 1 1+(689355033/5000000000 : ℝ)*X 1 2+(9322046537/10000000000 : ℝ)*X 2 0+(-356473979/10000000000 : ℝ)*X 2 1+(689355033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((7878247/312500000 : ℝ)*X 0 0+(-9931351157/10000000000 : ℝ)*X 0 1+(-44618061/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((-1046299/10000000000 : ℝ)*X 1 0+(-1022870731/5000000000 : ℝ)*X 1 1+(902491947/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((8070991243/10000000000 : ℝ)*X 2 0+(586959129/10000000000 : ℝ)*X 2 1+(98131063/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((925705927/1000000000 : ℝ)*X 0 0+(-494410389/10000000000 : ℝ)*X 0 1+(349893117/2500000000 : ℝ)*X 0 2+(925705927/1000000000 : ℝ)*X 1 0+(-494410389/10000000000 : ℝ)*X 1 1+(349893117/2500000000 : ℝ)*X 1 2+(925705927/1000000000 : ℝ)*X 2 0+(-494410389/10000000000 : ℝ)*X 2 1+(349893117/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((4097171/10000000000 : ℝ)*X 0 0+(-9996750179/10000000000 : ℝ)*X 0 1+(12309693/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((71238311/5000000000 : ℝ)*X 1 0+(-3100204193/5000000000 : ℝ)*X 1 1+(-5530482681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((8491587357/10000000000 : ℝ)*X 2 0+(244964101/10000000000 : ℝ)*X 2 1+(2748084787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((553150851/625000000 : ℝ)*X 0 0+(-35156053/1000000000 : ℝ)*X 0 1+(1081558951/5000000000 : ℝ)*X 0 2+(553150851/625000000 : ℝ)*X 1 0+(-35156053/1000000000 : ℝ)*X 1 1+(1081558951/5000000000 : ℝ)*X 1 2+(553150851/625000000 : ℝ)*X 2 0+(-35156053/1000000000 : ℝ)*X 2 1+(1081558951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((13515039/500000000 : ℝ)*X 0 0+(-9930475463/10000000000 : ℝ)*X 0 1+(3465593/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((148927047/5000000000 : ℝ)*X 1 0+(-216686251/2000000000 : ℝ)*X 1 1+(-950072859/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((4164914519/5000000000 : ℝ)*X 2 0+(59927487/625000000 : ℝ)*X 2 1+(2532356467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((4695051171/5000000000 : ℝ)*X 0 0+(-149588563/2000000000 : ℝ)*X 0 1+(469251769/5000000000 : ℝ)*X 0 2+(4695051171/5000000000 : ℝ)*X 1 0+(-149588563/2000000000 : ℝ)*X 1 1+(469251769/5000000000 : ℝ)*X 1 2+(4695051171/5000000000 : ℝ)*X 2 0+(-149588563/2000000000 : ℝ)*X 2 1+(469251769/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((3551/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 2+(3551/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1825011360844233839877/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (703830949979/200000000000 : ℝ)*(base7) + (1278963/1000000000000 : ℝ)*(base33) + (834638714381/1000000000000 : ℝ)*(base44) + (3141516919229/500000000000 : ℝ)*(base53) + (1518921/1000000000000 : ℝ)*(base59) + (1974327492633/250000000000 : ℝ)*(major_s0_0) + (3531336267557/500000000000 : ℝ)*(major_s0_1) + (1614277411037/1000000000000 : ℝ)*(major_s0_2) + (2101514920833/1000000000000 : ℝ)*(sp_s0_7) + (126687492749/100000000000 : ℝ)*(sp_s0_8) + (8384528962817/1000000000000 : ℝ)*(sp_s0_9) + (7891322339451/1000000000000 : ℝ)*(sp_s0_13) + (18517511/1000000000000 : ℝ)*(sp_s0_23) + (14502409/500000000000 : ℝ)*(sp_s0_27) + (1041367061751/200000000000 : ℝ)*(f.failure) + (8384548759291/1000000000000 : ℝ)*(f.sum) + (439412574443159/2000000000000000000000000000 : ℝ)*base62 + (15138327145959/50000000000000000000000000 : ℝ)*base64 + (43505777110011/1000000000000000000000000000 : ℝ)*base67 + (762205733956841/2000000000000000000000000000 : ℝ)*base69 + (965951158071/25000000000000000000000000 : ℝ)*base71 + (57619983572563/250000000000000000000000000 : ℝ)*base72 + (35350381/400000000000000000000 : ℝ)*base75 + (4632138295183/50000000000000000000000000 : ℝ)*base77 + (17569004194139/1000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (291/2500000000000000 : ℝ)*base86 + (291/2500000000000000 : ℝ)*base88 + (291/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((7629/10000 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(7629/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1854551554476622705071/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53478314161/20000000000 : ℝ)*(base7) + (367492882971/500000000000 : ℝ)*(base33) + (540286881709/125000000000 : ℝ)*(base53) + (407618619397/1000000000000 : ℝ)*(base59) + (5806703344471/1000000000000 : ℝ)*(major_s0_0) + (6541689110413/1000000000000 : ℝ)*(major_s0_1) + (2219394056741/1000000000000 : ℝ)*(major_s0_2) + (560153/1000000000000 : ℝ)*(sp_s0_1) + (4659719/500000000000 : ℝ)*(sp_s0_2) + (13227969/500000000000 : ℝ)*(sp_s0_13) + (2773971725319/1000000000000 : ℝ)*(sp_s0_14) + (254873174903/125000000000 : ℝ)*(sp_s0_15) + (1590317923403/250000000000 : ℝ)*(sp_s0_16) + (1746734798921/250000000000 : ℝ)*(sp_s0_20) + (4313049943571/1000000000000 : ℝ)*(f.failure) + (7096266778991/1000000000000 : ℝ)*(f.sum) + (1413373576035887/2000000000000000000000000000 : ℝ)*base62 + (30199413642431/100000000000000000000000000 : ℝ)*base64 + (417170225561331/2000000000000000000000000000 : ℝ)*base66 + (1258625716435887/2000000000000000000000000000 : ℝ)*base68 + (15662610005523/100000000000000000000000000 : ℝ)*base70 + (607820293800337/2000000000000000000000000000 : ℝ)*base72 + (1568991353/1250000000000000000000 : ℝ)*base74 + (834263896023/50000000000000000000000000 : ℝ)*base77 + (146462729720747/500000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (89/12500000000000000 : ℝ)*base87 + (89/12500000000000000 : ℝ)*base89 + (89/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-35167/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-35167/100000 : ℝ)*X 1 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3910645494041507249871/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4559445158933/1000000000000 : ℝ)*(base7) + (446954019657/500000000000 : ℝ)*(base33) + (6673/125000000000 : ℝ)*(base40) + (846872539701/1000000000000 : ℝ)*(base44) + (6080528761103/1000000000000 : ℝ)*(base53) + (57126007349/250000000000 : ℝ)*(base59) + (1414787764949/200000000000 : ℝ)*(major_s0_0) + (3560487162179/500000000000 : ℝ)*(major_s0_1) + (377463620591/200000000000 : ℝ)*(major_s0_2) + (5845863/250000000000 : ℝ)*(sp_s0_6) + (1747289857241/1000000000000 : ℝ)*(sp_s0_21) + (3254639113/500000000000 : ℝ)*(sp_s0_22) + (693391057903/100000000000 : ℝ)*(sp_s0_23) + (2241472476949/250000000000 : ℝ)*(sp_s0_27) + (1050668134403/200000000000 : ℝ)*(f.failure) + (978477327293/125000000000 : ℝ)*(f.sum) + (355597906517837/400000000000000000000000000 : ℝ)*base62 + (41683770575927/50000000000000000000000000 : ℝ)*base65 + (41539893286403/1000000000000000000000000000 : ℝ)*base66 + (366326277077837/400000000000000000000000000 : ℝ)*base68 + (14928456561063/20000000000000000000000000 : ℝ)*base71 + (225979317037283/400000000000000000000000000 : ℝ)*base72 + (826404637/1250000000000000000000 : ℝ)*base74 + (48056081747169/100000000000000000000000000 : ℝ)*base77 + (919961833975821/2000000000000000000000000000 : ℝ)*base78 + (1023/2500000000000000 : ℝ)*base86 + (1023/2500000000000000 : ℝ)*base88 + (1477/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (3551/4000 : ℝ) ^ (33/8 : ℝ) ≤ (30596310763250183563/50000000000000000000 : ℝ) := by
    have hpowers : (3551/4000 : ℝ)^33 ≤ (30596310763250183563/50000000000000000000 : ℝ)^8 := by
      have hnat : (3551 : ℕ)^33*50000000000000000000^8 ≤ 30596310763250183563^8*4000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3551 4000 30596310763250183563 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3551/4000 : ℝ)) (X := (30596310763250183563/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (80596310763250183563/50000000000000000000 : ℝ) ≤ (2245409152883089/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (80596310763250183563/50000000000000000000 : ℝ)^8 ≤ (2245409152883089/2000000000000000 : ℝ)^33 := by
      have hnat : (80596310763250183563 : ℕ)^8*2000000000000000^33 ≤ 2245409152883089^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80596310763250183563 50000000000000000000 2245409152883089 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2245409152883089/2000000000000000 : ℝ)) (X := (80596310763250183563/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (55596310763250183563/25000000000000000000 : ℝ) ≤ (6068996750734761/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (55596310763250183563/25000000000000000000 : ℝ)^8 ≤ (6068996750734761/5000000000000000 : ℝ)^33 := by
      have hnat : (55596310763250183563 : ℕ)^8*5000000000000000^33 ≤ 6068996750734761^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55596310763250183563 25000000000000000000 6068996750734761 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6068996750734761/5000000000000000 : ℝ)) (X := (55596310763250183563/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(245409152883089/1775500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2))+(910947737054077/8877500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (3551/4000 : ℝ)) (alpha := (245409152883089/1775500000000000 : ℝ)) (beta := (910947737054077/8877500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 2, 1], ![0, 2, 1], ![1, 0, 2]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 2) ≤ (3551/4000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(245409152883089/1775500000000000 : ℝ)*((1 : ℝ)*pair X 0 2)+(910947737054077/8877500000000000 : ℝ)*((1 : ℝ)*pair X 0 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (7629/10000 : ℝ) ^ (33/8 : ℝ) ≤ (8186889338659890273/25000000000000000000 : ℝ) := by
    have hpowers : (7629/10000 : ℝ)^33 ≤ (8186889338659890273/25000000000000000000 : ℝ)^8 := by
      have hnat : (7629 : ℕ)^33*25000000000000000000^8 ≤ 8186889338659890273^8*10000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7629 10000 8186889338659890273 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7629/10000 : ℝ)) (X := (8186889338659890273/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (33186889338659890273/25000000000000000000 : ℝ) ≤ (2677716681042349/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (33186889338659890273/25000000000000000000 : ℝ)^8 ≤ (2677716681042349/2500000000000000 : ℝ)^33 := by
      have hnat : (33186889338659890273 : ℕ)^8*2500000000000000^33 ≤ 2677716681042349^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33186889338659890273 25000000000000000000 2677716681042349 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2677716681042349/2500000000000000 : ℝ)) (X := (33186889338659890273/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (20686889338659890273/12500000000000000000 : ℝ) ≤ (2259793872764141/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (20686889338659890273/12500000000000000000 : ℝ)^8 ≤ (2259793872764141/2000000000000000 : ℝ)^33 := by
      have hnat : (20686889338659890273 : ℕ)^8*2000000000000000^33 ≤ 2259793872764141^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20686889338659890273 12500000000000000000 2259793872764141 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2259793872764141/2000000000000000 : ℝ)) (X := (20686889338659890273/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 0+X 2 0))+(59238893680783/635750000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(196034213217103/2543000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (7629/10000 : ℝ)) (alpha := (59238893680783/635750000000000 : ℝ)) (beta := (196034213217103/2543000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 2, 1], ![0, 2, 1], ![1, 0, 2]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (7629/10000 : ℝ)*((1 : ℝ)*pair X 1 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 0)+(59238893680783/635750000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(196034213217103/2543000000000000 : ℝ)*((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (35167/100000 : ℝ) ^ (33/8 : ℝ) ≤ (335543020434287039/25000000000000000000 : ℝ) := by
    have hpowers : (35167/100000 : ℝ)^33 ≤ (335543020434287039/25000000000000000000 : ℝ)^8 := by
      have hnat : (35167 : ℕ)^33*25000000000000000000^8 ≤ 335543020434287039^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35167 100000 335543020434287039 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35167/100000 : ℝ)) (X := (335543020434287039/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (25335543020434287039/25000000000000000000 : ℝ) ≤ (10032373373640923/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (25335543020434287039/25000000000000000000 : ℝ)^8 ≤ (10032373373640923/10000000000000000 : ℝ)^33 := by
      have hnat : (25335543020434287039 : ℕ)^8*10000000000000000^33 ≤ 10032373373640923^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25335543020434287039 25000000000000000000 10032373373640923 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10032373373640923/10000000000000000 : ℝ)) (X := (25335543020434287039/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12835543020434287039/12500000000000000000 : ℝ) ≤ (10064423546385407/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (12835543020434287039/12500000000000000000 : ℝ)^8 ≤ (10064423546385407/10000000000000000 : ℝ)^33 := by
      have hnat : (12835543020434287039 : ℕ)^8*10000000000000000^33 ≤ 10064423546385407^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12835543020434287039 12500000000000000000 10064423546385407 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10064423546385407/10000000000000000 : ℝ)) (X := (12835543020434287039/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 1+X 1 1))+(32373373640923/3516700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(8012543186121/879175000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (35167/100000 : ℝ)) (alpha := (32373373640923/3516700000000000 : ℝ)) (beta := (8012543186121/879175000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 2, 1], ![0, 2, 1], ![1, 0, 2]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (35167/100000 : ℝ)*((-1 : ℝ)*pair X 2 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 1)+(32373373640923/3516700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(8012543186121/879175000000000 : ℝ)*((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((4079717/5000000000 : ℝ)*X 0 0+(-9997848003/10000000000 : ℝ)*X 0 1+(-7131043/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((-23948723/1250000000 : ℝ)*X 1 0+(-2406834751/2500000000 : ℝ)*X 1 1+(449002113/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((9345662957/10000000000 : ℝ)*X 2 0+(386299143/10000000000 : ℝ)*X 2 1+(1315805869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4823907063/5000000000 : ℝ)*X 0 0+(-19249409/1250000000 : ℝ)*X 0 1+(439034883/5000000000 : ℝ)*X 0 2+(4823907063/5000000000 : ℝ)*X 1 0+(-19249409/1250000000 : ℝ)*X 1 1+(439034883/5000000000 : ℝ)*X 1 2+(4823907063/5000000000 : ℝ)*X 2 0+(-19249409/1250000000 : ℝ)*X 2 1+(439034883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c201273_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-38127/6250 : ℝ) < ((-18959/12500 : ℝ)*P 0+(-18959/12500 : ℝ)*P 1+(-18959/12500 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-38127/6250 : ℝ) < (-936338106924075367851819363138963819/158782398615500000000000000000000000 : ℝ) := by norm_num
    linear_combination (144846696971/250000000000 : ℝ)*(base7) + (13734003/1000000000000 : ℝ)*(base10) + (12036735307/100000000000 : ℝ)*(base33) + (441/200000000000 : ℝ)*(base39) + (106759780329/1000000000000 : ℝ)*(base44) + (351922577567/500000000000 : ℝ)*(base53) + (202676159/50000000000 : ℝ)*(base60) + (33687/1000000000000 : ℝ)*(ratio_s0_0) + (139635264693/100000000000 : ℝ)*(major_s1_0) + (1409960219671/1000000000000 : ℝ)*(major_s1_1) + (406437422433/500000000000 : ℝ)*(major_s1_2) + (224766881803/250000000000 : ℝ)*(sp_s1_0) + (83994265977/125000000000 : ℝ)*(sp_s1_1) + (1482559063279/1000000000000 : ℝ)*(sp_s1_2) + (368156751889/250000000000 : ℝ)*(sp_s1_6) + (1602926416349/1000000000000 : ℝ)*(f.sum) + (1828507924317781/1758350000000000000000000000 : ℝ)*base62 + (968091644099287/2543000000000000000000000000 : ℝ)*base65 + (8439588783066172949/22357420250000000000000000000000 : ℝ)*base66 + (1415673763174861/1758350000000000000000000000 : ℝ)*base68 + (423577641585761/887750000000000000000000000 : ℝ)*base71 + (188769713093666633/6243900850000000000000000000000 : ℝ)*base72 + (12712292059/10000000000000000000000 : ℝ)*base74 + (3128972572725969329/9030193000000000000000000000000 : ℝ)*base77 + (345423958951601323/2257548250000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_repeated_p001_b106 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 323) (hlo : 273 ≤ c.val) (hhi : c.val < 274)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by
  have hc : c=273 := by omega
  rcases hc with rfl
  · exact collision_c201273 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 323) (hlo : 273 ≤ c.val) (hhi : c.val < 274)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X (repeatedOrders c) (repeatedSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p001_b106 p hpa hpb c hlo hhi X hX

#print axioms solution

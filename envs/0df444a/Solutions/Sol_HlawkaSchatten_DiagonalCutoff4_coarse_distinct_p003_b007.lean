-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b007
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:54:01.966312+00:00
-- url     : https://prove2.me/submissions/64c94dc1-c105-418d-9273-a221804660f1

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
theorem collision_support_c303016_s0_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-5235914321/10000000000 : ℝ)*x 0 + (40622709/156250000 : ℝ)*x 1 + (-199072923/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5235914321/10000000000 : ℝ)^135 ≤ (42824198162253/100000000000000 : ℝ)^103 := by
    have hnat : (5235914321 : ℕ)^135*100000000000000^103 ≤ 42824198162253^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235914321 10000000000 42824198162253 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40622709/156250000 : ℝ)^135 ≤ (8553727247171/50000000000000 : ℝ)^103 := by
    have hnat : (40622709 : ℕ)^135*50000000000000^103 ≤ 8553727247171^103*156250000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40622709 156250000 8553727247171 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199072923/400000000 : ℝ)^135 ≤ (40068347326007/100000000000000 : ℝ)^103 := by
    have hnat : (199072923 : ℕ)^135*100000000000000^103 ≤ 40068347326007^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199072923 400000000 40068347326007 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5235914321/10000000000 : ℝ), (40622709/156250000 : ℝ), (-199072923/400000000 : ℝ)] ![(42824198162253/100000000000000 : ℝ), (8553727247171/50000000000000 : ℝ), (40068347326007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5235914321/10000000000 : ℝ)|^135 ≤ (42824198162253/100000000000000 : ℝ)^103
        have hw : |(-5235914321/10000000000 : ℝ)|=(5235914321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40622709/156250000 : ℝ)|^135 ≤ (8553727247171/50000000000000 : ℝ)^103
        have hw : |(40622709/156250000 : ℝ)|=(40622709/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199072923/400000000 : ℝ)|^135 ≤ (40068347326007/100000000000000 : ℝ)^103
        have hw : |(-199072923/400000000 : ℝ)|=(199072923/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s0_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4965450887/10000000000 : ℝ)*x 0 + (-21911343/62500000 : ℝ)*x 1 + (-4463191061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4965450887/10000000000 : ℝ)^135 ≤ (19974193789889/50000000000000 : ℝ)^103 := by
    have hnat : (4965450887 : ℕ)^135*50000000000000^103 ≤ 19974193789889^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4965450887 10000000000 19974193789889 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21911343/62500000 : ℝ)^135 ≤ (25314199422119/100000000000000 : ℝ)^103 := by
    have hnat : (21911343 : ℕ)^135*100000000000000^103 ≤ 25314199422119^103*62500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21911343 62500000 25314199422119 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4463191061/10000000000 : ℝ)^135 ≤ (4342176623393/12500000000000 : ℝ)^103 := by
    have hnat : (4463191061 : ℕ)^135*12500000000000^103 ≤ 4342176623393^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4463191061 10000000000 4342176623393 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4965450887/10000000000 : ℝ), (-21911343/62500000 : ℝ), (-4463191061/10000000000 : ℝ)] ![(19974193789889/50000000000000 : ℝ), (25314199422119/100000000000000 : ℝ), (4342176623393/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4965450887/10000000000 : ℝ)|^135 ≤ (19974193789889/50000000000000 : ℝ)^103
        have hw : |(4965450887/10000000000 : ℝ)|=(4965450887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21911343/62500000 : ℝ)|^135 ≤ (25314199422119/100000000000000 : ℝ)^103
        have hw : |(-21911343/62500000 : ℝ)|=(21911343/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4463191061/10000000000 : ℝ)|^135 ≤ (4342176623393/12500000000000 : ℝ)^103
        have hw : |(-4463191061/10000000000 : ℝ)|=(4463191061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s0_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (888178263/2500000000 : ℝ)*x 0 + (1480285583/2500000000 : ℝ)*x 1 + (3358172187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (888178263/2500000000 : ℝ)^135 ≤ (201241876389/781250000000 : ℝ)^103 := by
    have hnat : (888178263 : ℕ)^135*781250000000^103 ≤ 201241876389^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888178263 2500000000 201241876389 781250000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1480285583/2500000000 : ℝ)^135 ≤ (50314890295119/100000000000000 : ℝ)^103 := by
    have hnat : (1480285583 : ℕ)^135*100000000000000^103 ≤ 50314890295119^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1480285583 2500000000 50314890295119 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3358172187/10000000000 : ℝ)^135 ≤ (2990768688343/12500000000000 : ℝ)^103 := by
    have hnat : (3358172187 : ℕ)^135*12500000000000^103 ≤ 2990768688343^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3358172187 10000000000 2990768688343 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(888178263/2500000000 : ℝ), (1480285583/2500000000 : ℝ), (3358172187/10000000000 : ℝ)] ![(201241876389/781250000000 : ℝ), (50314890295119/100000000000000 : ℝ), (2990768688343/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(888178263/2500000000 : ℝ)|^135 ≤ (201241876389/781250000000 : ℝ)^103
        have hw : |(888178263/2500000000 : ℝ)|=(888178263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1480285583/2500000000 : ℝ)|^135 ≤ (50314890295119/100000000000000 : ℝ)^103
        have hw : |(1480285583/2500000000 : ℝ)|=(1480285583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3358172187/10000000000 : ℝ)|^135 ≤ (2990768688343/12500000000000 : ℝ)^103
        have hw : |(3358172187/10000000000 : ℝ)|=(3358172187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s0_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2398915591/10000000000 : ℝ)*x 0 + (1480285583/2500000000 : ℝ)*x 1 + (-4419210693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2398915591/10000000000 : ℝ)^135 ≤ (15395658093907/100000000000000 : ℝ)^103 := by
    have hnat : (2398915591 : ℕ)^135*100000000000000^103 ≤ 15395658093907^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2398915591 10000000000 15395658093907 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1480285583/2500000000 : ℝ)^135 ≤ (50314890295119/100000000000000 : ℝ)^103 := by
    have hnat : (1480285583 : ℕ)^135*100000000000000^103 ≤ 50314890295119^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1480285583 2500000000 50314890295119 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4419210693/10000000000 : ℝ)^135 ≤ (34289451591427/100000000000000 : ℝ)^103 := by
    have hnat : (4419210693 : ℕ)^135*100000000000000^103 ≤ 34289451591427^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419210693 10000000000 34289451591427 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2398915591/10000000000 : ℝ), (1480285583/2500000000 : ℝ), (-4419210693/10000000000 : ℝ)] ![(15395658093907/100000000000000 : ℝ), (50314890295119/100000000000000 : ℝ), (34289451591427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2398915591/10000000000 : ℝ)|^135 ≤ (15395658093907/100000000000000 : ℝ)^103
        have hw : |(2398915591/10000000000 : ℝ)|=(2398915591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1480285583/2500000000 : ℝ)|^135 ≤ (50314890295119/100000000000000 : ℝ)^103
        have hw : |(1480285583/2500000000 : ℝ)|=(1480285583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4419210693/10000000000 : ℝ)|^135 ≤ (34289451591427/100000000000000 : ℝ)^103
        have hw : |(-4419210693/10000000000 : ℝ)|=(4419210693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s0_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-329957411/625000000 : ℝ)*x 0 + (611684913/2500000000 : ℝ)*x 1 + (-5056455943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329957411/625000000 : ℝ)^135 ≤ (8658017632723/20000000000000 : ℝ)^103 := by
    have hnat : (329957411 : ℕ)^135*20000000000000^103 ≤ 8658017632723^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329957411 625000000 8658017632723 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (611684913/2500000000 : ℝ)^135 ≤ (3949794054033/25000000000000 : ℝ)^103 := by
    have hnat : (611684913 : ℕ)^135*25000000000000^103 ≤ 3949794054033^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611684913 2500000000 3949794054033 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5056455943/10000000000 : ℝ)^135 ≤ (4091073561159/10000000000000 : ℝ)^103 := by
    have hnat : (5056455943 : ℕ)^135*10000000000000^103 ≤ 4091073561159^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5056455943 10000000000 4091073561159 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-329957411/625000000 : ℝ), (611684913/2500000000 : ℝ), (-5056455943/10000000000 : ℝ)] ![(8658017632723/20000000000000 : ℝ), (3949794054033/25000000000000 : ℝ), (4091073561159/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-329957411/625000000 : ℝ)|^135 ≤ (8658017632723/20000000000000 : ℝ)^103
        have hw : |(-329957411/625000000 : ℝ)|=(329957411/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(611684913/2500000000 : ℝ)|^135 ≤ (3949794054033/25000000000000 : ℝ)^103
        have hw : |(611684913/2500000000 : ℝ)|=(611684913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5056455943/10000000000 : ℝ)|^135 ≤ (4091073561159/10000000000000 : ℝ)^103
        have hw : |(-5056455943/10000000000 : ℝ)|=(5056455943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s0_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2494497493/5000000000 : ℝ)*x 0 + (-405354947/1250000000 : ℝ)*x 1 + (-467832023/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2494497493/5000000000 : ℝ)^135 ≤ (20098418675251/50000000000000 : ℝ)^103 := by
    have hnat : (2494497493 : ℕ)^135*50000000000000^103 ≤ 20098418675251^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2494497493 5000000000 20098418675251 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (405354947/1250000000 : ℝ)^135 ≤ (11427467166811/50000000000000 : ℝ)^103 := by
    have hnat : (405354947 : ℕ)^135*50000000000000^103 ≤ 11427467166811^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405354947 1250000000 11427467166811 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467832023/1000000000 : ℝ)^135 ≤ (7389645658691/20000000000000 : ℝ)^103 := by
    have hnat : (467832023 : ℕ)^135*20000000000000^103 ≤ 7389645658691^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467832023 1000000000 7389645658691 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2494497493/5000000000 : ℝ), (-405354947/1250000000 : ℝ), (-467832023/1000000000 : ℝ)] ![(20098418675251/50000000000000 : ℝ), (11427467166811/50000000000000 : ℝ), (7389645658691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2494497493/5000000000 : ℝ)|^135 ≤ (20098418675251/50000000000000 : ℝ)^103
        have hw : |(2494497493/5000000000 : ℝ)|=(2494497493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-405354947/1250000000 : ℝ)|^135 ≤ (11427467166811/50000000000000 : ℝ)^103
        have hw : |(-405354947/1250000000 : ℝ)|=(405354947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467832023/1000000000 : ℝ)|^135 ≤ (7389645658691/20000000000000 : ℝ)^103
        have hw : |(-467832023/1000000000 : ℝ)|=(467832023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s0_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (210328827/625000000 : ℝ)*x 0 + (775206611/1250000000 : ℝ)*x 1 + (200582567/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210328827/625000000 : ℝ)^135 ≤ (23992370615829/100000000000000 : ℝ)^103 := by
    have hnat : (210328827 : ℕ)^135*100000000000000^103 ≤ 23992370615829^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210328827 625000000 23992370615829 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (775206611/1250000000 : ℝ)^135 ≤ (53461821477031/100000000000000 : ℝ)^103 := by
    have hnat : (775206611 : ℕ)^135*100000000000000^103 ≤ 53461821477031^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775206611 1250000000 53461821477031 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200582567/625000000 : ℝ)^135 ≤ (22545807897503/100000000000000 : ℝ)^103 := by
    have hnat : (200582567 : ℕ)^135*100000000000000^103 ≤ 22545807897503^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200582567 625000000 22545807897503 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210328827/625000000 : ℝ), (775206611/1250000000 : ℝ), (200582567/625000000 : ℝ)] ![(23992370615829/100000000000000 : ℝ), (53461821477031/100000000000000 : ℝ), (22545807897503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210328827/625000000 : ℝ)|^135 ≤ (23992370615829/100000000000000 : ℝ)^103
        have hw : |(210328827/625000000 : ℝ)|=(210328827/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(775206611/1250000000 : ℝ)|^135 ≤ (53461821477031/100000000000000 : ℝ)^103
        have hw : |(775206611/1250000000 : ℝ)|=(775206611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(200582567/625000000 : ℝ)|^135 ≤ (22545807897503/100000000000000 : ℝ)^103
        have hw : |(200582567/625000000 : ℝ)|=(200582567/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s0_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (463103779/2000000000 : ℝ)*x 0 + (775206611/1250000000 : ℝ)*x 1 + (-835254763/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (463103779/2000000000 : ℝ)^135 ≤ (14697975493479/100000000000000 : ℝ)^103 := by
    have hnat : (463103779 : ℕ)^135*100000000000000^103 ≤ 14697975493479^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463103779 2000000000 14697975493479 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (775206611/1250000000 : ℝ)^135 ≤ (53461821477031/100000000000000 : ℝ)^103 := by
    have hnat : (775206611 : ℕ)^135*100000000000000^103 ≤ 53461821477031^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775206611 1250000000 53461821477031 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (835254763/2000000000 : ℝ)^135 ≤ (31840203015643/100000000000000 : ℝ)^103 := by
    have hnat : (835254763 : ℕ)^135*100000000000000^103 ≤ 31840203015643^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835254763 2000000000 31840203015643 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(463103779/2000000000 : ℝ), (775206611/1250000000 : ℝ), (-835254763/2000000000 : ℝ)] ![(14697975493479/100000000000000 : ℝ), (53461821477031/100000000000000 : ℝ), (31840203015643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(463103779/2000000000 : ℝ)|^135 ≤ (14697975493479/100000000000000 : ℝ)^103
        have hw : |(463103779/2000000000 : ℝ)|=(463103779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(775206611/1250000000 : ℝ)|^135 ≤ (53461821477031/100000000000000 : ℝ)^103
        have hw : |(775206611/1250000000 : ℝ)|=(775206611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-835254763/2000000000 : ℝ)|^135 ≤ (31840203015643/100000000000000 : ℝ)^103
        have hw : |(-835254763/2000000000 : ℝ)|=(835254763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s0_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-5289627427/10000000000 : ℝ)*x 0 + (38508917/156250000 : ℝ)*x 1 + (-5031739089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289627427/10000000000 : ℝ)^135 ≤ (43400916052897/100000000000000 : ℝ)^103 := by
    have hnat : (5289627427 : ℕ)^135*100000000000000^103 ≤ 43400916052897^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289627427 10000000000 43400916052897 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38508917/156250000 : ℝ)^135 ≤ (996891086979/6250000000000 : ℝ)^103 := by
    have hnat : (38508917 : ℕ)^135*6250000000000^103 ≤ 996891086979^103*156250000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38508917 156250000 996891086979 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5031739089/10000000000 : ℝ)^135 ≤ (10162206636953/25000000000000 : ℝ)^103 := by
    have hnat : (5031739089 : ℕ)^135*25000000000000^103 ≤ 10162206636953^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5031739089 10000000000 10162206636953 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5289627427/10000000000 : ℝ), (38508917/156250000 : ℝ), (-5031739089/10000000000 : ℝ)] ![(43400916052897/100000000000000 : ℝ), (996891086979/6250000000000 : ℝ), (10162206636953/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5289627427/10000000000 : ℝ)|^135 ≤ (43400916052897/100000000000000 : ℝ)^103
        have hw : |(-5289627427/10000000000 : ℝ)|=(5289627427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38508917/156250000 : ℝ)|^135 ≤ (996891086979/6250000000000 : ℝ)^103
        have hw : |(38508917/156250000 : ℝ)|=(38508917/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5031739089/10000000000 : ℝ)|^135 ≤ (10162206636953/25000000000000 : ℝ)^103
        have hw : |(-5031739089/10000000000 : ℝ)|=(5031739089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s0_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2553939643/5000000000 : ℝ)*x 0 + (-3546301833/10000000000 : ℝ)*x 1 + (-1069114833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2553939643/5000000000 : ℝ)^135 ≤ (8291382134577/20000000000000 : ℝ)^103 := by
    have hnat : (2553939643 : ℕ)^135*20000000000000^103 ≤ 8291382134577^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2553939643 5000000000 8291382134577 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3546301833/10000000000 : ℝ)^135 ≤ (2569805088731/10000000000000 : ℝ)^103 := by
    have hnat : (3546301833 : ℕ)^135*10000000000000^103 ≤ 2569805088731^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3546301833 10000000000 2569805088731 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1069114833/2500000000 : ℝ)^135 ≤ (32845038430601/100000000000000 : ℝ)^103 := by
    have hnat : (1069114833 : ℕ)^135*100000000000000^103 ≤ 32845038430601^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069114833 2500000000 32845038430601 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2553939643/5000000000 : ℝ), (-3546301833/10000000000 : ℝ), (-1069114833/2500000000 : ℝ)] ![(8291382134577/20000000000000 : ℝ), (2569805088731/10000000000000 : ℝ), (32845038430601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2553939643/5000000000 : ℝ)|^135 ≤ (8291382134577/20000000000000 : ℝ)^103
        have hw : |(2553939643/5000000000 : ℝ)|=(2553939643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3546301833/10000000000 : ℝ)|^135 ≤ (2569805088731/10000000000000 : ℝ)^103
        have hw : |(-3546301833/10000000000 : ℝ)|=(3546301833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1069114833/2500000000 : ℝ)|^135 ≤ (32845038430601/100000000000000 : ℝ)^103
        have hw : |(-1069114833/2500000000 : ℝ)|=(1069114833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s0_16 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (21719907/62500000 : ℝ)*x 0 + (6051831721/10000000000 : ℝ)*x 1 + (820028737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21719907/62500000 : ℝ)^135 ≤ (12512357782857/50000000000000 : ℝ)^103 := by
    have hnat : (21719907 : ℕ)^135*50000000000000^103 ≤ 12512357782857^103*62500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21719907 62500000 12512357782857 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6051831721/10000000000 : ℝ)^135 ≤ (12943852080767/25000000000000 : ℝ)^103 := by
    have hnat : (6051831721 : ℕ)^135*25000000000000^103 ≤ 12943852080767^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6051831721 10000000000 12943852080767 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (820028737/2500000000 : ℝ)^135 ≤ (23199876101377/100000000000000 : ℝ)^103 := by
    have hnat : (820028737 : ℕ)^135*100000000000000^103 ≤ 23199876101377^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820028737 2500000000 23199876101377 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21719907/62500000 : ℝ), (6051831721/10000000000 : ℝ), (820028737/2500000000 : ℝ)] ![(12512357782857/50000000000000 : ℝ), (12943852080767/25000000000000 : ℝ), (23199876101377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21719907/62500000 : ℝ)|^135 ≤ (12512357782857/50000000000000 : ℝ)^103
        have hw : |(21719907/62500000 : ℝ)|=(21719907/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6051831721/10000000000 : ℝ)|^135 ≤ (12943852080767/25000000000000 : ℝ)^103
        have hw : |(6051831721/10000000000 : ℝ)|=(6051831721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(820028737/2500000000 : ℝ)|^135 ≤ (23199876101377/100000000000000 : ℝ)^103
        have hw : |(820028737/2500000000 : ℝ)|=(820028737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s0_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (41855563/200000000 : ℝ)*x 0 + (5802545333/10000000000 : ℝ)*x 1 + (-4791931369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41855563/200000000 : ℝ)^135 ≤ (1287317690823/10000000000000 : ℝ)^103 := by
    have hnat : (41855563 : ℕ)^135*10000000000000^103 ≤ 1287317690823^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41855563 200000000 1287317690823 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5802545333/10000000000 : ℝ)^135 ≤ (48998145451971/100000000000000 : ℝ)^103 := by
    have hnat : (5802545333 : ℕ)^135*100000000000000^103 ≤ 48998145451971^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5802545333 10000000000 48998145451971 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4791931369/10000000000 : ℝ)^135 ≤ (4766084702867/12500000000000 : ℝ)^103 := by
    have hnat : (4791931369 : ℕ)^135*12500000000000^103 ≤ 4766084702867^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4791931369 10000000000 4766084702867 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41855563/200000000 : ℝ), (5802545333/10000000000 : ℝ), (-4791931369/10000000000 : ℝ)] ![(1287317690823/10000000000000 : ℝ), (48998145451971/100000000000000 : ℝ), (4766084702867/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41855563/200000000 : ℝ)|^135 ≤ (1287317690823/10000000000000 : ℝ)^103
        have hw : |(41855563/200000000 : ℝ)|=(41855563/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5802545333/10000000000 : ℝ)|^135 ≤ (48998145451971/100000000000000 : ℝ)^103
        have hw : |(5802545333/10000000000 : ℝ)|=(5802545333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4791931369/10000000000 : ℝ)|^135 ≤ (4766084702867/12500000000000 : ℝ)^103
        have hw : |(-4791931369/10000000000 : ℝ)|=(4791931369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s0_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2724019597/5000000000 : ℝ)*x 0 + (19513433/80000000 : ℝ)*x 1 + (-4889787699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2724019597/5000000000 : ℝ)^135 ≤ (45112348677871/100000000000000 : ℝ)^103 := by
    have hnat : (2724019597 : ℕ)^135*100000000000000^103 ≤ 45112348677871^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724019597 5000000000 45112348677871 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19513433/80000000 : ℝ)^135 ≤ (15735219429893/100000000000000 : ℝ)^103 := by
    have hnat : (19513433 : ℕ)^135*100000000000000^103 ≤ 15735219429893^103*80000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19513433 80000000 15735219429893 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4889787699/10000000000 : ℝ)^135 ≤ (9788107971299/25000000000000 : ℝ)^103 := by
    have hnat : (4889787699 : ℕ)^135*25000000000000^103 ≤ 9788107971299^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4889787699 10000000000 9788107971299 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2724019597/5000000000 : ℝ), (19513433/80000000 : ℝ), (-4889787699/10000000000 : ℝ)] ![(45112348677871/100000000000000 : ℝ), (15735219429893/100000000000000 : ℝ), (9788107971299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2724019597/5000000000 : ℝ)|^135 ≤ (45112348677871/100000000000000 : ℝ)^103
        have hw : |(-2724019597/5000000000 : ℝ)|=(2724019597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(19513433/80000000 : ℝ)|^135 ≤ (15735219429893/100000000000000 : ℝ)^103
        have hw : |(19513433/80000000 : ℝ)|=(19513433/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4889787699/10000000000 : ℝ)|^135 ≤ (9788107971299/25000000000000 : ℝ)^103
        have hw : |(-4889787699/10000000000 : ℝ)|=(4889787699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s0_22 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1191969347/2500000000 : ℝ)*x 0 + (-1815070543/5000000000 : ℝ)*x 1 + (-2274956729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1191969347/2500000000 : ℝ)^135 ≤ (37878017358503/100000000000000 : ℝ)^103 := by
    have hnat : (1191969347 : ℕ)^135*100000000000000^103 ≤ 37878017358503^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191969347 2500000000 37878017358503 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1815070543/5000000000 : ℝ)^135 ≤ (828038883657/3125000000000 : ℝ)^103 := by
    have hnat : (1815070543 : ℕ)^135*3125000000000^103 ≤ 828038883657^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815070543 5000000000 828038883657 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2274956729/5000000000 : ℝ)^135 ≤ (17812369177841/50000000000000 : ℝ)^103 := by
    have hnat : (2274956729 : ℕ)^135*50000000000000^103 ≤ 17812369177841^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274956729 5000000000 17812369177841 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1191969347/2500000000 : ℝ), (-1815070543/5000000000 : ℝ), (-2274956729/5000000000 : ℝ)] ![(37878017358503/100000000000000 : ℝ), (828038883657/3125000000000 : ℝ), (17812369177841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1191969347/2500000000 : ℝ)|^135 ≤ (37878017358503/100000000000000 : ℝ)^103
        have hw : |(1191969347/2500000000 : ℝ)|=(1191969347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1815070543/5000000000 : ℝ)|^135 ≤ (828038883657/3125000000000 : ℝ)^103
        have hw : |(-1815070543/5000000000 : ℝ)|=(1815070543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2274956729/5000000000 : ℝ)|^135 ≤ (17812369177841/50000000000000 : ℝ)^103
        have hw : |(-2274956729/5000000000 : ℝ)|=(2274956729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s0_23 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1812746221/5000000000 : ℝ)*x 0 + (598543171/1000000000 : ℝ)*x 1 + (3205985773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1812746221/5000000000 : ℝ)^135 ≤ (26452779756631/100000000000000 : ℝ)^103 := by
    have hnat : (1812746221 : ℕ)^135*100000000000000^103 ≤ 26452779756631^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812746221 5000000000 26452779756631 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598543171/1000000000 : ℝ)^135 ≤ (51032117662337/100000000000000 : ℝ)^103 := by
    have hnat : (598543171 : ℕ)^135*100000000000000^103 ≤ 51032117662337^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598543171 1000000000 51032117662337 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3205985773/10000000000 : ℝ)^135 ≤ (5628775641017/25000000000000 : ℝ)^103 := by
    have hnat : (3205985773 : ℕ)^135*25000000000000^103 ≤ 5628775641017^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3205985773 10000000000 5628775641017 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1812746221/5000000000 : ℝ), (598543171/1000000000 : ℝ), (3205985773/10000000000 : ℝ)] ![(26452779756631/100000000000000 : ℝ), (51032117662337/100000000000000 : ℝ), (5628775641017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1812746221/5000000000 : ℝ)|^135 ≤ (26452779756631/100000000000000 : ℝ)^103
        have hw : |(1812746221/5000000000 : ℝ)|=(1812746221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598543171/1000000000 : ℝ)|^135 ≤ (51032117662337/100000000000000 : ℝ)^103
        have hw : |(598543171/1000000000 : ℝ)|=(598543171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3205985773/10000000000 : ℝ)|^135 ≤ (5628775641017/25000000000000 : ℝ)^103
        have hw : |(3205985773/10000000000 : ℝ)|=(3205985773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s0_27 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (197033751/1000000000 : ℝ)*x 0 + (598543171/1000000000 : ℝ)*x 1 + (-469034617/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197033751/1000000000 : ℝ)^135 ≤ (11895118713141/100000000000000 : ℝ)^103 := by
    have hnat : (197033751 : ℕ)^135*100000000000000^103 ≤ 11895118713141^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197033751 1000000000 11895118713141 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598543171/1000000000 : ℝ)^135 ≤ (51032117662337/100000000000000 : ℝ)^103 := by
    have hnat : (598543171 : ℕ)^135*100000000000000^103 ≤ 51032117662337^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598543171 1000000000 51032117662337 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (469034617/1000000000 : ℝ)^135 ≤ (4634095451319/12500000000000 : ℝ)^103 := by
    have hnat : (469034617 : ℕ)^135*12500000000000^103 ≤ 4634095451319^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469034617 1000000000 4634095451319 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(197033751/1000000000 : ℝ), (598543171/1000000000 : ℝ), (-469034617/1000000000 : ℝ)] ![(11895118713141/100000000000000 : ℝ), (51032117662337/100000000000000 : ℝ), (4634095451319/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(197033751/1000000000 : ℝ)|^135 ≤ (11895118713141/100000000000000 : ℝ)^103
        have hw : |(197033751/1000000000 : ℝ)|=(197033751/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598543171/1000000000 : ℝ)|^135 ≤ (51032117662337/100000000000000 : ℝ)^103
        have hw : |(598543171/1000000000 : ℝ)|=(598543171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-469034617/1000000000 : ℝ)|^135 ≤ (4634095451319/12500000000000 : ℝ)^103
        have hw : |(-469034617/1000000000 : ℝ)|=(469034617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s1_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-4590736329/10000000000 : ℝ)*x 0 + (3777051441/10000000000 : ℝ)*x 1 + (-229536817/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4590736329/10000000000 : ℝ)^135 ≤ (7208851593521/20000000000000 : ℝ)^103 := by
    have hnat : (4590736329 : ℕ)^135*20000000000000^103 ≤ 7208851593521^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4590736329 10000000000 7208851593521 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3777051441/10000000000 : ℝ)^135 ≤ (13955741969679/50000000000000 : ℝ)^103 := by
    have hnat : (3777051441 : ℕ)^135*50000000000000^103 ≤ 13955741969679^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3777051441 10000000000 13955741969679 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229536817/500000000 : ℝ)^135 ≤ (9011064520201/25000000000000 : ℝ)^103 := by
    have hnat : (229536817 : ℕ)^135*25000000000000^103 ≤ 9011064520201^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229536817 500000000 9011064520201 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4590736329/10000000000 : ℝ), (3777051441/10000000000 : ℝ), (-229536817/500000000 : ℝ)] ![(7208851593521/20000000000000 : ℝ), (13955741969679/50000000000000 : ℝ), (9011064520201/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4590736329/10000000000 : ℝ)|^135 ≤ (7208851593521/20000000000000 : ℝ)^103
        have hw : |(-4590736329/10000000000 : ℝ)|=(4590736329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3777051441/10000000000 : ℝ)|^135 ≤ (13955741969679/50000000000000 : ℝ)^103
        have hw : |(3777051441/10000000000 : ℝ)|=(3777051441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-229536817/500000000 : ℝ)|^135 ≤ (9011064520201/25000000000000 : ℝ)^103
        have hw : |(-229536817/500000000 : ℝ)|=(229536817/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s1_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4590736329/10000000000 : ℝ)*x 0 + (-3777051441/10000000000 : ℝ)*x 1 + (-229536817/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4590736329/10000000000 : ℝ)^135 ≤ (7208851593521/20000000000000 : ℝ)^103 := by
    have hnat : (4590736329 : ℕ)^135*20000000000000^103 ≤ 7208851593521^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4590736329 10000000000 7208851593521 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3777051441/10000000000 : ℝ)^135 ≤ (13955741969679/50000000000000 : ℝ)^103 := by
    have hnat : (3777051441 : ℕ)^135*50000000000000^103 ≤ 13955741969679^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3777051441 10000000000 13955741969679 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229536817/500000000 : ℝ)^135 ≤ (9011064520201/25000000000000 : ℝ)^103 := by
    have hnat : (229536817 : ℕ)^135*25000000000000^103 ≤ 9011064520201^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229536817 500000000 9011064520201 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4590736329/10000000000 : ℝ), (-3777051441/10000000000 : ℝ), (-229536817/500000000 : ℝ)] ![(7208851593521/20000000000000 : ℝ), (13955741969679/50000000000000 : ℝ), (9011064520201/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4590736329/10000000000 : ℝ)|^135 ≤ (7208851593521/20000000000000 : ℝ)^103
        have hw : |(4590736329/10000000000 : ℝ)|=(4590736329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3777051441/10000000000 : ℝ)|^135 ≤ (13955741969679/50000000000000 : ℝ)^103
        have hw : |(-3777051441/10000000000 : ℝ)|=(3777051441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-229536817/500000000 : ℝ)|^135 ≤ (9011064520201/25000000000000 : ℝ)^103
        have hw : |(-229536817/500000000 : ℝ)|=(229536817/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s1_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3954686687/10000000000 : ℝ)*x 0 + (5037624217/10000000000 : ℝ)*x 1 + (494335837/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3954686687/10000000000 : ℝ)^135 ≤ (7411106062537/25000000000000 : ℝ)^103 := by
    have hnat : (3954686687 : ℕ)^135*25000000000000^103 ≤ 7411106062537^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3954686687 10000000000 7411106062537 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5037624217/10000000000 : ℝ)^135 ≤ (40711151396517/100000000000000 : ℝ)^103 := by
    have hnat : (5037624217 : ℕ)^135*100000000000000^103 ≤ 40711151396517^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5037624217 10000000000 40711151396517 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (494335837/1250000000 : ℝ)^135 ≤ (7411106084643/25000000000000 : ℝ)^103 := by
    have hnat : (494335837 : ℕ)^135*25000000000000^103 ≤ 7411106084643^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494335837 1250000000 7411106084643 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3954686687/10000000000 : ℝ), (5037624217/10000000000 : ℝ), (494335837/1250000000 : ℝ)] ![(7411106062537/25000000000000 : ℝ), (40711151396517/100000000000000 : ℝ), (7411106084643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3954686687/10000000000 : ℝ)|^135 ≤ (7411106062537/25000000000000 : ℝ)^103
        have hw : |(3954686687/10000000000 : ℝ)|=(3954686687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5037624217/10000000000 : ℝ)|^135 ≤ (40711151396517/100000000000000 : ℝ)^103
        have hw : |(5037624217/10000000000 : ℝ)|=(5037624217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(494335837/1250000000 : ℝ)|^135 ≤ (7411106084643/25000000000000 : ℝ)^103
        have hw : |(494335837/1250000000 : ℝ)|=(494335837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303016_s1_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3954686687/10000000000 : ℝ)*x 0 + (5037624217/10000000000 : ℝ)*x 1 + (-494335837/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3954686687/10000000000 : ℝ)^135 ≤ (7411106062537/25000000000000 : ℝ)^103 := by
    have hnat : (3954686687 : ℕ)^135*25000000000000^103 ≤ 7411106062537^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3954686687 10000000000 7411106062537 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5037624217/10000000000 : ℝ)^135 ≤ (40711151396517/100000000000000 : ℝ)^103 := by
    have hnat : (5037624217 : ℕ)^135*100000000000000^103 ≤ 40711151396517^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5037624217 10000000000 40711151396517 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (494335837/1250000000 : ℝ)^135 ≤ (7411106084643/25000000000000 : ℝ)^103 := by
    have hnat : (494335837 : ℕ)^135*25000000000000^103 ≤ 7411106084643^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494335837 1250000000 7411106084643 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3954686687/10000000000 : ℝ), (5037624217/10000000000 : ℝ), (-494335837/1250000000 : ℝ)] ![(7411106062537/25000000000000 : ℝ), (40711151396517/100000000000000 : ℝ), (7411106084643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3954686687/10000000000 : ℝ)|^135 ≤ (7411106062537/25000000000000 : ℝ)^103
        have hw : |(3954686687/10000000000 : ℝ)|=(3954686687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5037624217/10000000000 : ℝ)|^135 ≤ (40711151396517/100000000000000 : ℝ)^103
        have hw : |(5037624217/10000000000 : ℝ)|=(5037624217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-494335837/1250000000 : ℝ)|^135 ≤ (7411106084643/25000000000000 : ℝ)^103
        have hw : |(-494335837/1250000000 : ℝ)|=(494335837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303016 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-5235914321/10000000000 : ℝ)*X 0 0+(40622709/156250000 : ℝ)*X 0 1+(-199072923/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4965450887/10000000000 : ℝ)*X 1 0+(-21911343/62500000 : ℝ)*X 1 1+(-4463191061/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((888178263/2500000000 : ℝ)*X 2 0+(1480285583/2500000000 : ℝ)*X 2 1+(3358172187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((2398915591/10000000000 : ℝ)*X 0 0+(1480285583/2500000000 : ℝ)*X 0 1+(-4419210693/10000000000 : ℝ)*X 0 2+(2398915591/10000000000 : ℝ)*X 1 0+(1480285583/2500000000 : ℝ)*X 1 1+(-4419210693/10000000000 : ℝ)*X 1 2+(2398915591/10000000000 : ℝ)*X 2 0+(1480285583/2500000000 : ℝ)*X 2 1+(-4419210693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-329957411/625000000 : ℝ)*X 0 0+(611684913/2500000000 : ℝ)*X 0 1+(-5056455943/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2494497493/5000000000 : ℝ)*X 1 0+(-405354947/1250000000 : ℝ)*X 1 1+(-467832023/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((210328827/625000000 : ℝ)*X 2 0+(775206611/1250000000 : ℝ)*X 2 1+(200582567/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((463103779/2000000000 : ℝ)*X 0 0+(775206611/1250000000 : ℝ)*X 0 1+(-835254763/2000000000 : ℝ)*X 0 2+(463103779/2000000000 : ℝ)*X 1 0+(775206611/1250000000 : ℝ)*X 1 1+(-835254763/2000000000 : ℝ)*X 1 2+(463103779/2000000000 : ℝ)*X 2 0+(775206611/1250000000 : ℝ)*X 2 1+(-835254763/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-5289627427/10000000000 : ℝ)*X 0 0+(38508917/156250000 : ℝ)*X 0 1+(-5031739089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2553939643/5000000000 : ℝ)*X 1 0+(-3546301833/10000000000 : ℝ)*X 1 1+(-1069114833/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((21719907/62500000 : ℝ)*X 2 0+(6051831721/10000000000 : ℝ)*X 2 1+(820028737/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((41855563/200000000 : ℝ)*X 0 0+(5802545333/10000000000 : ℝ)*X 0 1+(-4791931369/10000000000 : ℝ)*X 0 2+(41855563/200000000 : ℝ)*X 1 0+(5802545333/10000000000 : ℝ)*X 1 1+(-4791931369/10000000000 : ℝ)*X 1 2+(41855563/200000000 : ℝ)*X 2 0+(5802545333/10000000000 : ℝ)*X 2 1+(-4791931369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-2724019597/5000000000 : ℝ)*X 0 0+(19513433/80000000 : ℝ)*X 0 1+(-4889787699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1191969347/2500000000 : ℝ)*X 1 0+(-1815070543/5000000000 : ℝ)*X 1 1+(-2274956729/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((1812746221/5000000000 : ℝ)*X 2 0+(598543171/1000000000 : ℝ)*X 2 1+(3205985773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((197033751/1000000000 : ℝ)*X 0 0+(598543171/1000000000 : ℝ)*X 0 1+(-469034617/1000000000 : ℝ)*X 0 2+(197033751/1000000000 : ℝ)*X 1 0+(598543171/1000000000 : ℝ)*X 1 1+(-469034617/1000000000 : ℝ)*X 1 2+(197033751/1000000000 : ℝ)*X 2 0+(598543171/1000000000 : ℝ)*X 2 1+(-469034617/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1079/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1079/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8801456116493768088273/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (549230514993/500000000000 : ℝ)*(base5) + (878340274957/250000000000 : ℝ)*(base50) + (3147503913827/1000000000000 : ℝ)*(base59) + (2490361/200000000000 : ℝ)*(base60) + (3582113149253/200000000000 : ℝ)*(major_s0_0) + (3582113149253/200000000000 : ℝ)*(major_s0_1) + (3582113149253/200000000000 : ℝ)*(major_s0_2) + (33228593/1000000000000 : ℝ)*(sp_s0_1) + (23914091099413/1000000000000 : ℝ)*(sp_s0_7) + (23913961394081/1000000000000 : ℝ)*(sp_s0_8) + (25012552129399/1000000000000 : ℝ)*(sp_s0_9) + (1080833347523/100000000000 : ℝ)*(sp_s0_13) + (96476739/1000000000000 : ℝ)*(sp_s0_22) + (121477037/500000000000 : ℝ)*(sp_s0_27) + (1190703745929/100000000000 : ℝ)*(f.failure) + (23914091099413/1000000000000 : ℝ)*(f.sum) + (110585619373833/200000000000000000000000000 : ℝ)*base62 + (146358554866843/250000000000000000000000000 : ℝ)*base65 + (63645556508157/250000000000000000000000000 : ℝ)*base66 + (52932027506167/400000000000000000000000000 : ℝ)*base69 + (511864730803909/2000000000000000000000000000 : ℝ)*base71 + (92272473891843/250000000000000000000000000 : ℝ)*base72 + (97276348346167/400000000000000000000000000 : ℝ)*base75 + (284785601653833/400000000000000000000000000 : ℝ)*base77 + (1395251651/5000000000000000000000 : ℝ)*base79 + (491/500000000000000 : ℝ)*base86 + (491/500000000000000 : ℝ)*base88 + (491/500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3679/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(3679/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1215832470397024457361/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78423001517/250000000000 : ℝ)*(base1) + (771541385521/500000000000 : ℝ)*(base50) + (383847857007/200000000000 : ℝ)*(base59) + (583286914997/50000000000 : ℝ)*(major_s0_0) + (583286914997/50000000000 : ℝ)*(major_s0_1) + (583286914997/50000000000 : ℝ)*(major_s0_2) + (206483673/500000000000 : ℝ)*(sp_s0_2) + (9236949/500000000000 : ℝ)*(sp_s0_6) + (1388598427/1000000000000 : ℝ)*(sp_s0_7) + (15888333140821/1000000000000 : ℝ)*(sp_s0_14) + (778801486659/50000000000 : ℝ)*(sp_s0_15) + (778769811589/50000000000 : ℝ)*(sp_s0_16) + (116277080383/15625000000 : ℝ)*(sp_s0_20) + (110267027/500000000000 : ℝ)*(sp_s0_23) + (3877721812239/500000000000 : ℝ)*(f.failure) + (778801486659/50000000000 : ℝ)*(f.sum) + (13161110730417/50000000000000000000000000 : ℝ)*base62 + (4343292699907/62500000000000000000000000 : ℝ)*base65 + (10102273049907/62500000000000000000000000 : ℝ)*base67 + (3075875715417/100000000000000000000000000 : ℝ)*base68 + (26117479876341/500000000000000000000000000 : ℝ)*base71 + (3553139287593/62500000000000000000000000 : ℝ)*base73 + (21704115515417/100000000000000000000000000 : ℝ)*base74 + (5241276504583/100000000000000000000000000 : ℝ)*base76 + (1066460679/5000000000000000000000 : ℝ)*base79 + (481/2500000000000000 : ℝ)*base86 + (481/2500000000000000 : ℝ)*base88 + (481/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-8437/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-8437/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (38127748742332101643209/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (154112035941/500000000000 : ℝ)*(base1) + (1203932201813/1000000000000 : ℝ)*(base5) + (575931/1000000000000 : ℝ)*(base39) + (2798703170179/1000000000000 : ℝ)*(base50) + (614635446943/200000000000 : ℝ)*(base59) + (14654029007549/1000000000000 : ℝ)*(major_s0_0) + (14654029007549/1000000000000 : ℝ)*(major_s0_1) + (14654029007549/1000000000000 : ℝ)*(major_s0_2) + (90156637/1000000000000 : ℝ)*(sp_s0_0) + (326327357/1000000000000 : ℝ)*(sp_s0_13) + (397482239691/20000000000 : ℝ)*(sp_s0_21) + (3913195613861/200000000000 : ℝ)*(sp_s0_22) + (10384955135559/500000000000 : ℝ)*(sp_s0_23) + (1028699032629/125000000000 : ℝ)*(sp_s0_27) + (1948414972417/200000000000 : ℝ)*(f.failure) + (3913195613861/200000000000 : ℝ)*(f.sum) + (321101917390689/1000000000000000000000000000 : ℝ)*base62 + (900179490604019/1250000000000000000000000000 : ℝ)*base65 + (19068317854019/1250000000000000000000000000 : ℝ)*base67 + (190245813409311/2000000000000000000000000000 : ℝ)*base69 + (7685751174785597/10000000000000000000000000000 : ℝ)*base71 + (693110229729019/1250000000000000000000000000 : ℝ)*base72 + (464457149790689/2000000000000000000000000000 : ℝ)*base74 + (1163128248390689/2000000000000000000000000000 : ℝ)*base77 + (1642099819/10000000000000000000000 : ℝ)*base78 + (743/1000000000000000 : ℝ)*base86 + (743/1000000000000000 : ℝ)*base88 + (743/1000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (1079/6250 : ℝ) ^ (131/32 : ℝ) ≤ (75343834333173367/100000000000000000000 : ℝ) := by
    have hpowers : (1079/6250 : ℝ)^131 ≤ (75343834333173367/100000000000000000000 : ℝ)^32 := by
      have hnat : (1079 : ℕ)^131*100000000000000000000^32 ≤ 75343834333173367^32*6250^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1079 6250 75343834333173367 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1079/6250 : ℝ)) (X := (75343834333173367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100075343834333173367/100000000000000000000 : ℝ) ≤ (5000919968167153/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (100075343834333173367/100000000000000000000 : ℝ)^32 ≤ (5000919968167153/5000000000000000 : ℝ)^131 := by
      have hnat : (100075343834333173367 : ℕ)^32*5000000000000000^131 ≤ 5000919968167153^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100075343834333173367 100000000000000000000 5000919968167153 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000919968167153/5000000000000000 : ℝ)) (X := (100075343834333173367/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50075343834333173367/50000000000000000000 : ℝ) ≤ (5001839413054663/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50075343834333173367/50000000000000000000 : ℝ)^32 ≤ (5001839413054663/5000000000000000 : ℝ)^131 := by
      have hnat : (50075343834333173367 : ℕ)^32*5000000000000000^131 ≤ 5001839413054663^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50075343834333173367 50000000000000000000 5001839413054663 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001839413054663/5000000000000000 : ℝ)) (X := (50075343834333173367/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(919968167153/863200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(91944488751/86320000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1079/6250 : ℝ)) (alpha := (919968167153/863200000000000 : ℝ)) (beta := (91944488751/86320000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1079/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(919968167153/863200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(91944488751/86320000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (3679/50000 : ℝ) ^ (131/32 : ℝ) ≤ (2295080186378941/100000000000000000000 : ℝ) := by
    have hpowers : (3679/50000 : ℝ)^131 ≤ (2295080186378941/100000000000000000000 : ℝ)^32 := by
      have hnat : (3679 : ℕ)^131*100000000000000000000^32 ≤ 2295080186378941^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3679 50000 2295080186378941 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3679/50000 : ℝ)) (X := (2295080186378941/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100002295080186378941/100000000000000000000 : ℝ) ≤ (2500014015635317/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (100002295080186378941/100000000000000000000 : ℝ)^32 ≤ (2500014015635317/2500000000000000 : ℝ)^131 := by
      have hnat : (100002295080186378941 : ℕ)^32*2500000000000000^131 ≤ 2500014015635317^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100002295080186378941 100000000000000000000 2500014015635317 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500014015635317/2500000000000000 : ℝ)) (X := (100002295080186378941/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50002295080186378941/50000000000000000000 : ℝ) ≤ (1000011212411019/1000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50002295080186378941/50000000000000000000 : ℝ)^32 ≤ (1000011212411019/1000000000000000 : ℝ)^131 := by
      have hnat : (50002295080186378941 : ℕ)^32*1000000000000000^131 ≤ 1000011212411019^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002295080186378941 50000000000000000000 1000011212411019 1000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000011212411019/1000000000000000 : ℝ)) (X := (50002295080186378941/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(14015635317/183950000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(28030784461/367900000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (3679/50000 : ℝ)) (alpha := (14015635317/183950000000000 : ℝ)) (beta := (28030784461/367900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (3679/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(14015635317/183950000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(28030784461/367900000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (8437/100000 : ℝ) ^ (131/32 : ℝ) ≤ (4018669826175011/100000000000000000000 : ℝ) := by
    have hpowers : (8437/100000 : ℝ)^131 ≤ (4018669826175011/100000000000000000000 : ℝ)^32 := by
      have hnat : (8437 : ℕ)^131*100000000000000000000^32 ≤ 4018669826175011^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8437 100000 4018669826175011 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8437/100000 : ℝ)) (X := (4018669826175011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100004018669826175011/100000000000000000000 : ℝ) ≤ (10000098164489867/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (100004018669826175011/100000000000000000000 : ℝ)^32 ≤ (10000098164489867/10000000000000000 : ℝ)^131 := by
      have hnat : (100004018669826175011 : ℕ)^32*10000000000000000^131 ≤ 10000098164489867^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100004018669826175011 100000000000000000000 10000098164489867 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000098164489867/10000000000000000 : ℝ)) (X := (100004018669826175011/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50004018669826175011/50000000000000000000 : ℝ) ≤ (10000196325998633/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50004018669826175011/50000000000000000000 : ℝ)^32 ≤ (10000196325998633/10000000000000000 : ℝ)^131 := by
      have hnat : (50004018669826175011 : ℕ)^32*10000000000000000^131 ≤ 10000196325998633^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004018669826175011 50000000000000000000 10000196325998633 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000196325998633/10000000000000000 : ℝ)) (X := (50004018669826175011/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1663804913/14300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(49080754383/421850000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (8437/100000 : ℝ)) (alpha := (1663804913/14300000000000 : ℝ)) (beta := (49080754383/421850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (8437/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1663804913/14300000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(49080754383/421850000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-4590736329/10000000000 : ℝ)*X 0 0+(3777051441/10000000000 : ℝ)*X 0 1+(-229536817/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4590736329/10000000000 : ℝ)*X 1 0+(-3777051441/10000000000 : ℝ)*X 1 1+(-229536817/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3954686687/10000000000 : ℝ)*X 2 0+(5037624217/10000000000 : ℝ)*X 2 1+(494335837/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3954686687/10000000000 : ℝ)*X 0 0+(5037624217/10000000000 : ℝ)*X 0 1+(-494335837/1250000000 : ℝ)*X 0 2+(3954686687/10000000000 : ℝ)*X 1 0+(5037624217/10000000000 : ℝ)*X 1 1+(-494335837/1250000000 : ℝ)*X 1 2+(3954686687/10000000000 : ℝ)*X 2 0+(5037624217/10000000000 : ℝ)*X 2 1+(-494335837/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303016_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15063/2500 : ℝ) < ((-7521/5000 : ℝ)*P 0+(-7521/5000 : ℝ)*P 1+(-7521/5000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15063/2500 : ℝ) < (-20893778653551681222033860277/3501355000000000000000000000 : ℝ) := by norm_num
    linear_combination (8973/1000000000000 : ℝ)*(base8) + (13871/1000000000000 : ℝ)*(base29) + (48494877723/250000000000 : ℝ)*(base39) + (126288283949/1000000000000 : ℝ)*(base49) + (321984617473/1000000000000 : ℝ)*(base50) + (444370836513/1000000000000 : ℝ)*(base59) + (195406712811/1000000000000 : ℝ)*(base60) + (5523/1000000000000 : ℝ)*(ratio_s0_0) + (7521/5000 : ℝ)*(major_s1_0) + (7521/5000 : ℝ)*(major_s1_1) + (7521/5000 : ℝ)*(major_s1_2) + (497278400297/250000000000 : ℝ)*(sp_s1_0) + (1989113610161/1000000000000 : ℝ)*(sp_s1_1) + (1989113610161/1000000000000 : ℝ)*(sp_s1_2) + (999999986129/1000000000000 : ℝ)*(sp_s1_6) + (1989113610161/1000000000000 : ℝ)*(f.sum) + (235540467746599/404690000000000000000000000 : ℝ)*base62 + (62925897309263/84370000000000000000000000 : ℝ)*base65 + (128851067623/4598750000000000000000000 : ℝ)*base66 + (45862564207/178750000000000000000000 : ℝ)*base68 + (629921718566021/875338750000000000000000000 : ℝ)*base71 + (390817993849/2697500000000000000000000 : ℝ)*base73 + (584548866483/3679000000000000000000000 : ℝ)*base75 + (444616453053/1079000000000000000000000 : ℝ)*base77 + (17538694073389/47712031250000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p003_b007 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 16 ≤ c.val) (hhi : c.val < 17)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=16 := by omega
  rcases hc with rfl
  · exact collision_c303016 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 16 ≤ c.val) (hhi : c.val < 17)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b007 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

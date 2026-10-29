-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313062_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:34:53.346198+00:00
-- url     : https://prove2.me/submissions/1906141f-529c-4c13-9f10-5f892f9f9e39

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
theorem collision_support_c313062_s2_s2_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-469852923/2500000000 : ℝ)*x 0 + (4905482621/10000000000 : ℝ)*x 1 + (-5611238537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (469852923/2500000000 : ℝ)^37 ≤ (2962730299609/25000000000000 : ℝ)^29 := by
    have hnat : (469852923 : ℕ)^37*25000000000000^29 ≤ 2962730299609^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469852923 2500000000 2962730299609 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4905482621/10000000000 : ℝ)^37 ≤ (5038051233747/12500000000000 : ℝ)^29 := by
    have hnat : (4905482621 : ℕ)^37*12500000000000^29 ≤ 5038051233747^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4905482621 10000000000 5038051233747 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5611238537/10000000000 : ℝ)^37 ≤ (9568933782907/20000000000000 : ℝ)^29 := by
    have hnat : (5611238537 : ℕ)^37*20000000000000^29 ≤ 9568933782907^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5611238537 10000000000 9568933782907 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-469852923/2500000000 : ℝ), (4905482621/10000000000 : ℝ), (-5611238537/10000000000 : ℝ)] ![(2962730299609/25000000000000 : ℝ), (5038051233747/12500000000000 : ℝ), (9568933782907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-469852923/2500000000 : ℝ)|^37 ≤ (2962730299609/25000000000000 : ℝ)^29
        have hw : |(-469852923/2500000000 : ℝ)|=(469852923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4905482621/10000000000 : ℝ)|^37 ≤ (5038051233747/12500000000000 : ℝ)^29
        have hw : |(4905482621/10000000000 : ℝ)|=(4905482621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5611238537/10000000000 : ℝ)|^37 ≤ (9568933782907/20000000000000 : ℝ)^29
        have hw : |(-5611238537/10000000000 : ℝ)|=(5611238537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s2_s2_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1226487137/2500000000 : ℝ)*x 0 + (-1881632097/10000000000 : ℝ)*x 1 + (-21910731/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1226487137/2500000000 : ℝ)^37 ≤ (8061858824521/20000000000000 : ℝ)^29 := by
    have hnat : (1226487137 : ℕ)^37*20000000000000^29 ≤ 8061858824521^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226487137 2500000000 8061858824521 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1881632097/10000000000 : ℝ)^37 ≤ (741799224391/6250000000000 : ℝ)^29 := by
    have hnat : (1881632097 : ℕ)^37*6250000000000^29 ≤ 741799224391^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881632097 10000000000 741799224391 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21910731/39062500 : ℝ)^37 ≤ (47821918279131/100000000000000 : ℝ)^29 := by
    have hnat : (21910731 : ℕ)^37*100000000000000^29 ≤ 47821918279131^29*39062500^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21910731 39062500 47821918279131 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1226487137/2500000000 : ℝ), (-1881632097/10000000000 : ℝ), (-21910731/39062500 : ℝ)] ![(8061858824521/20000000000000 : ℝ), (741799224391/6250000000000 : ℝ), (47821918279131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1226487137/2500000000 : ℝ)|^37 ≤ (8061858824521/20000000000000 : ℝ)^29
        have hw : |(1226487137/2500000000 : ℝ)|=(1226487137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1881632097/10000000000 : ℝ)|^37 ≤ (741799224391/6250000000000 : ℝ)^29
        have hw : |(-1881632097/10000000000 : ℝ)|=(1881632097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21910731/39062500 : ℝ)|^37 ≤ (47821918279131/100000000000000 : ℝ)^29
        have hw : |(-21910731/39062500 : ℝ)|=(21910731/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s2_s2_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5080219471/10000000000 : ℝ)*x 0 + (1270186791/2500000000 : ℝ)*x 1 + (1171716613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5080219471/10000000000 : ℝ)^37 ≤ (2107252656329/5000000000000 : ℝ)^29 := by
    have hnat : (5080219471 : ℕ)^37*5000000000000^29 ≤ 2107252656329^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080219471 10000000000 2107252656329 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270186791/2500000000 : ℝ)^37 ≤ (42150638541133/100000000000000 : ℝ)^29 := by
    have hnat : (1270186791 : ℕ)^37*100000000000000^29 ≤ 42150638541133^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270186791 2500000000 42150638541133 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1171716613/5000000000 : ℝ)^37 ≤ (7852154159113/50000000000000 : ℝ)^29 := by
    have hnat : (1171716613 : ℕ)^37*50000000000000^29 ≤ 7852154159113^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171716613 5000000000 7852154159113 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5080219471/10000000000 : ℝ), (1270186791/2500000000 : ℝ), (1171716613/5000000000 : ℝ)] ![(2107252656329/5000000000000 : ℝ), (42150638541133/100000000000000 : ℝ), (7852154159113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5080219471/10000000000 : ℝ)|^37 ≤ (2107252656329/5000000000000 : ℝ)^29
        have hw : |(5080219471/10000000000 : ℝ)|=(5080219471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270186791/2500000000 : ℝ)|^37 ≤ (42150638541133/100000000000000 : ℝ)^29
        have hw : |(1270186791/2500000000 : ℝ)|=(1270186791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1171716613/5000000000 : ℝ)|^37 ≤ (7852154159113/50000000000000 : ℝ)^29
        have hw : |(1171716613/5000000000 : ℝ)|=(1171716613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s2_s2_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1582191671/10000000000 : ℝ)*x 0 + (2245813661/5000000000 : ℝ)*x 1 + (-6211464493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1582191671/10000000000 : ℝ)^37 ≤ (2378510426749/25000000000000 : ℝ)^29 := by
    have hnat : (1582191671 : ℕ)^37*25000000000000^29 ≤ 2378510426749^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1582191671 10000000000 2378510426749 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245813661/5000000000 : ℝ)^37 ≤ (7203525207133/20000000000000 : ℝ)^29 := by
    have hnat : (2245813661 : ℕ)^37*20000000000000^29 ≤ 7203525207133^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245813661 5000000000 7203525207133 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6211464493/10000000000 : ℝ)^37 ≤ (27234166120587/50000000000000 : ℝ)^29 := by
    have hnat : (6211464493 : ℕ)^37*50000000000000^29 ≤ 27234166120587^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6211464493 10000000000 27234166120587 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1582191671/10000000000 : ℝ), (2245813661/5000000000 : ℝ), (-6211464493/10000000000 : ℝ)] ![(2378510426749/25000000000000 : ℝ), (7203525207133/20000000000000 : ℝ), (27234166120587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1582191671/10000000000 : ℝ)|^37 ≤ (2378510426749/25000000000000 : ℝ)^29
        have hw : |(-1582191671/10000000000 : ℝ)|=(1582191671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245813661/5000000000 : ℝ)|^37 ≤ (7203525207133/20000000000000 : ℝ)^29
        have hw : |(2245813661/5000000000 : ℝ)|=(2245813661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6211464493/10000000000 : ℝ)|^37 ≤ (27234166120587/50000000000000 : ℝ)^29
        have hw : |(-6211464493/10000000000 : ℝ)|=(6211464493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s2_s2_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (977108209/2000000000 : ℝ)*x 0 + (-655492303/5000000000 : ℝ)*x 1 + (-753450831/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977108209/2000000000 : ℝ)^37 ≤ (40095484967777/100000000000000 : ℝ)^29 := by
    have hnat : (977108209 : ℕ)^37*100000000000000^29 ≤ 40095484967777^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977108209 2000000000 40095484967777 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655492303/5000000000 : ℝ)^37 ≤ (7484731718727/100000000000000 : ℝ)^29 := by
    have hnat : (655492303 : ℕ)^37*100000000000000^29 ≤ 7484731718727^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655492303 5000000000 7484731718727 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (753450831/1250000000 : ℝ)^37 ≤ (52419783306943/100000000000000 : ℝ)^29 := by
    have hnat : (753450831 : ℕ)^37*100000000000000^29 ≤ 52419783306943^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753450831 1250000000 52419783306943 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(977108209/2000000000 : ℝ), (-655492303/5000000000 : ℝ), (-753450831/1250000000 : ℝ)] ![(40095484967777/100000000000000 : ℝ), (7484731718727/100000000000000 : ℝ), (52419783306943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(977108209/2000000000 : ℝ)|^37 ≤ (40095484967777/100000000000000 : ℝ)^29
        have hw : |(977108209/2000000000 : ℝ)|=(977108209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-655492303/5000000000 : ℝ)|^37 ≤ (7484731718727/100000000000000 : ℝ)^29
        have hw : |(-655492303/5000000000 : ℝ)|=(655492303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-753450831/1250000000 : ℝ)|^37 ≤ (52419783306943/100000000000000 : ℝ)^29
        have hw : |(-753450831/1250000000 : ℝ)|=(753450831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s2_s2_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2437932191/5000000000 : ℝ)*x 0 + (1464852577/2500000000 : ℝ)*x 1 + (1573191871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2437932191/5000000000 : ℝ)^37 ≤ (3999418870413/10000000000000 : ℝ)^29 := by
    have hnat : (2437932191 : ℕ)^37*10000000000000^29 ≤ 3999418870413^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2437932191 5000000000 3999418870413 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1464852577/2500000000 : ℝ)^37 ≤ (12640190491349/25000000000000 : ℝ)^29 := by
    have hnat : (1464852577 : ℕ)^37*25000000000000^29 ≤ 12640190491349^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464852577 2500000000 12640190491349 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1573191871/10000000000 : ℝ)^37 ≤ (1180631164407/12500000000000 : ℝ)^29 := by
    have hnat : (1573191871 : ℕ)^37*12500000000000^29 ≤ 1180631164407^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1573191871 10000000000 1180631164407 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2437932191/5000000000 : ℝ), (1464852577/2500000000 : ℝ), (1573191871/10000000000 : ℝ)] ![(3999418870413/10000000000000 : ℝ), (12640190491349/25000000000000 : ℝ), (1180631164407/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2437932191/5000000000 : ℝ)|^37 ≤ (3999418870413/10000000000000 : ℝ)^29
        have hw : |(2437932191/5000000000 : ℝ)|=(2437932191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1464852577/2500000000 : ℝ)|^37 ≤ (12640190491349/25000000000000 : ℝ)^29
        have hw : |(1464852577/2500000000 : ℝ)|=(1464852577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1573191871/10000000000 : ℝ)|^37 ≤ (1180631164407/12500000000000 : ℝ)^29
        have hw : |(1573191871/10000000000 : ℝ)|=(1573191871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s2_s2_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5161701073/10000000000 : ℝ)*x 0 + (602819963/1000000000 : ℝ)*x 1 + (-889682839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5161701073/10000000000 : ℝ)^37 ≤ (21504695404899/50000000000000 : ℝ)^29 := by
    have hnat : (5161701073 : ℕ)^37*50000000000000^29 ≤ 21504695404899^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161701073 10000000000 21504695404899 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (602819963/1000000000 : ℝ)^37 ≤ (26213181468287/50000000000000 : ℝ)^29 := by
    have hnat : (602819963 : ℕ)^37*50000000000000^29 ≤ 26213181468287^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602819963 1000000000 26213181468287 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (889682839/10000000000 : ℝ)^37 ≤ (912849246213/20000000000000 : ℝ)^29 := by
    have hnat : (889682839 : ℕ)^37*20000000000000^29 ≤ 912849246213^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889682839 10000000000 912849246213 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5161701073/10000000000 : ℝ), (602819963/1000000000 : ℝ), (-889682839/10000000000 : ℝ)] ![(21504695404899/50000000000000 : ℝ), (26213181468287/50000000000000 : ℝ), (912849246213/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5161701073/10000000000 : ℝ)|^37 ≤ (21504695404899/50000000000000 : ℝ)^29
        have hw : |(5161701073/10000000000 : ℝ)|=(5161701073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(602819963/1000000000 : ℝ)|^37 ≤ (26213181468287/50000000000000 : ℝ)^29
        have hw : |(602819963/1000000000 : ℝ)|=(602819963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-889682839/10000000000 : ℝ)|^37 ≤ (912849246213/20000000000000 : ℝ)^29
        have hw : |(-889682839/10000000000 : ℝ)|=(889682839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s2_s2_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1232590633/10000000000 : ℝ)*x 0 + (2399948877/5000000000 : ℝ)*x 1 + (-6158873561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1232590633/10000000000 : ℝ)^37 ≤ (3459236683957/50000000000000 : ℝ)^29 := by
    have hnat : (1232590633 : ℕ)^37*50000000000000^29 ≤ 3459236683957^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232590633 10000000000 3459236683957 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2399948877/5000000000 : ℝ)^37 ≤ (4900111874013/12500000000000 : ℝ)^29 := by
    have hnat : (2399948877 : ℕ)^37*12500000000000^29 ≤ 4900111874013^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399948877 5000000000 4900111874013 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6158873561/10000000000 : ℝ)^37 ≤ (13470157906529/25000000000000 : ℝ)^29 := by
    have hnat : (6158873561 : ℕ)^37*25000000000000^29 ≤ 13470157906529^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6158873561 10000000000 13470157906529 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1232590633/10000000000 : ℝ), (2399948877/5000000000 : ℝ), (-6158873561/10000000000 : ℝ)] ![(3459236683957/50000000000000 : ℝ), (4900111874013/12500000000000 : ℝ), (13470157906529/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1232590633/10000000000 : ℝ)|^37 ≤ (3459236683957/50000000000000 : ℝ)^29
        have hw : |(-1232590633/10000000000 : ℝ)|=(1232590633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2399948877/5000000000 : ℝ)|^37 ≤ (4900111874013/12500000000000 : ℝ)^29
        have hw : |(2399948877/5000000000 : ℝ)|=(2399948877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6158873561/10000000000 : ℝ)|^37 ≤ (13470157906529/25000000000000 : ℝ)^29
        have hw : |(-6158873561/10000000000 : ℝ)|=(6158873561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s2_s2_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2293947927/5000000000 : ℝ)*x 0 + (-10462823/62500000 : ℝ)*x 1 + (-378697831/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2293947927/5000000000 : ℝ)^37 ≤ (37005439351867/100000000000000 : ℝ)^29 := by
    have hnat : (2293947927 : ℕ)^37*100000000000000^29 ≤ 37005439351867^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293947927 5000000000 37005439351867 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10462823/62500000 : ℝ)^37 ≤ (10224360011121/100000000000000 : ℝ)^29 := by
    have hnat : (10462823 : ℕ)^37*100000000000000^29 ≤ 10224360011121^29*62500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10462823 62500000 10224360011121 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (378697831/625000000 : ℝ)^37 ≤ (10554040124271/20000000000000 : ℝ)^29 := by
    have hnat : (378697831 : ℕ)^37*20000000000000^29 ≤ 10554040124271^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378697831 625000000 10554040124271 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2293947927/5000000000 : ℝ), (-10462823/62500000 : ℝ), (-378697831/625000000 : ℝ)] ![(37005439351867/100000000000000 : ℝ), (10224360011121/100000000000000 : ℝ), (10554040124271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2293947927/5000000000 : ℝ)|^37 ≤ (37005439351867/100000000000000 : ℝ)^29
        have hw : |(2293947927/5000000000 : ℝ)|=(2293947927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10462823/62500000 : ℝ)|^37 ≤ (10224360011121/100000000000000 : ℝ)^29
        have hw : |(-10462823/62500000 : ℝ)|=(10462823/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-378697831/625000000 : ℝ)|^37 ≤ (10554040124271/20000000000000 : ℝ)^29
        have hw : |(-378697831/625000000 : ℝ)|=(378697831/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s2_s2_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5750508787/10000000000 : ℝ)*x 0 + (2487877013/5000000000 : ℝ)*x 1 + (1592421309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5750508787/10000000000 : ℝ)^37 ≤ (49364909626181/100000000000000 : ℝ)^29 := by
    have hnat : (5750508787 : ℕ)^37*100000000000000^29 ≤ 49364909626181^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5750508787 10000000000 49364909626181 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2487877013/5000000000 : ℝ)^37 ≤ (41042496789751/100000000000000 : ℝ)^29 := by
    have hnat : (2487877013 : ℕ)^37*100000000000000^29 ≤ 41042496789751^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2487877013 5000000000 41042496789751 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1592421309/10000000000 : ℝ)^37 ≤ (959259356713/10000000000000 : ℝ)^29 := by
    have hnat : (1592421309 : ℕ)^37*10000000000000^29 ≤ 959259356713^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592421309 10000000000 959259356713 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5750508787/10000000000 : ℝ), (2487877013/5000000000 : ℝ), (1592421309/10000000000 : ℝ)] ![(49364909626181/100000000000000 : ℝ), (41042496789751/100000000000000 : ℝ), (959259356713/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5750508787/10000000000 : ℝ)|^37 ≤ (49364909626181/100000000000000 : ℝ)^29
        have hw : |(5750508787/10000000000 : ℝ)|=(5750508787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2487877013/5000000000 : ℝ)|^37 ≤ (41042496789751/100000000000000 : ℝ)^29
        have hw : |(2487877013/5000000000 : ℝ)|=(2487877013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1592421309/10000000000 : ℝ)|^37 ≤ (959259356713/10000000000000 : ℝ)^29
        have hw : |(1592421309/10000000000 : ℝ)|=(1592421309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s2_s2_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6245729099/10000000000 : ℝ)*x 0 + (4929424859/10000000000 : ℝ)*x 1 + (-446995527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6245729099/10000000000 : ℝ)^37 ≤ (3428248570771/6250000000000 : ℝ)^29 := by
    have hnat : (6245729099 : ℕ)^37*6250000000000^29 ≤ 3428248570771^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6245729099 10000000000 3428248570771 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4929424859/10000000000 : ℝ)^37 ≤ (40555558735551/100000000000000 : ℝ)^29 := by
    have hnat : (4929424859 : ℕ)^37*100000000000000^29 ≤ 40555558735551^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4929424859 10000000000 40555558735551 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (446995527/5000000000 : ℝ)^37 ≤ (4592464124271/100000000000000 : ℝ)^29 := by
    have hnat : (446995527 : ℕ)^37*100000000000000^29 ≤ 4592464124271^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446995527 5000000000 4592464124271 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6245729099/10000000000 : ℝ), (4929424859/10000000000 : ℝ), (-446995527/5000000000 : ℝ)] ![(3428248570771/6250000000000 : ℝ), (40555558735551/100000000000000 : ℝ), (4592464124271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6245729099/10000000000 : ℝ)|^37 ≤ (3428248570771/6250000000000 : ℝ)^29
        have hw : |(6245729099/10000000000 : ℝ)|=(6245729099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4929424859/10000000000 : ℝ)|^37 ≤ (40555558735551/100000000000000 : ℝ)^29
        have hw : |(4929424859/10000000000 : ℝ)|=(4929424859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-446995527/5000000000 : ℝ)|^37 ≤ (4592464124271/100000000000000 : ℝ)^29
        have hw : |(-446995527/5000000000 : ℝ)|=(446995527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s2_s2_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-128391273/1250000000 : ℝ)*x 0 + (1311179069/2500000000 : ℝ)*x 1 + (-7331411/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128391273/1250000000 : ℝ)^37 ≤ (1096479334421/20000000000000 : ℝ)^29 := by
    have hnat : (128391273 : ℕ)^37*20000000000000^29 ≤ 1096479334421^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128391273 1250000000 1096479334421 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311179069/2500000000 : ℝ)^37 ≤ (43893875741321/100000000000000 : ℝ)^29 := by
    have hnat : (1311179069 : ℕ)^37*100000000000000^29 ≤ 43893875741321^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311179069 2500000000 43893875741321 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7331411/12500000 : ℝ)^37 ≤ (25311863785727/50000000000000 : ℝ)^29 := by
    have hnat : (7331411 : ℕ)^37*50000000000000^29 ≤ 25311863785727^29*12500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7331411 12500000 25311863785727 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-128391273/1250000000 : ℝ), (1311179069/2500000000 : ℝ), (-7331411/12500000 : ℝ)] ![(1096479334421/20000000000000 : ℝ), (43893875741321/100000000000000 : ℝ), (25311863785727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-128391273/1250000000 : ℝ)|^37 ≤ (1096479334421/20000000000000 : ℝ)^29
        have hw : |(-128391273/1250000000 : ℝ)|=(128391273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311179069/2500000000 : ℝ)|^37 ≤ (43893875741321/100000000000000 : ℝ)^29
        have hw : |(1311179069/2500000000 : ℝ)|=(1311179069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7331411/12500000 : ℝ)|^37 ≤ (25311863785727/50000000000000 : ℝ)^29
        have hw : |(-7331411/12500000 : ℝ)|=(7331411/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s2_s2_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (578111111/1000000000 : ℝ)*x 0 + (-1565286551/10000000000 : ℝ)*x 1 + (-4963647753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (578111111/1000000000 : ℝ)^37 ≤ (49700329238793/100000000000000 : ℝ)^29 := by
    have hnat : (578111111 : ℕ)^37*100000000000000^29 ≤ 49700329238793^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578111111 1000000000 49700329238793 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1565286551/10000000000 : ℝ)^37 ≤ (9384536935299/100000000000000 : ℝ)^29 := by
    have hnat : (1565286551 : ℕ)^37*100000000000000^29 ≤ 9384536935299^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1565286551 10000000000 9384536935299 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4963647753/10000000000 : ℝ)^37 ≤ (20457566906261/50000000000000 : ℝ)^29 := by
    have hnat : (4963647753 : ℕ)^37*50000000000000^29 ≤ 20457566906261^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4963647753 10000000000 20457566906261 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(578111111/1000000000 : ℝ), (-1565286551/10000000000 : ℝ), (-4963647753/10000000000 : ℝ)] ![(49700329238793/100000000000000 : ℝ), (9384536935299/100000000000000 : ℝ), (20457566906261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(578111111/1000000000 : ℝ)|^37 ≤ (49700329238793/100000000000000 : ℝ)^29
        have hw : |(578111111/1000000000 : ℝ)|=(578111111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1565286551/10000000000 : ℝ)|^37 ≤ (9384536935299/100000000000000 : ℝ)^29
        have hw : |(-1565286551/10000000000 : ℝ)|=(1565286551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4963647753/10000000000 : ℝ)|^37 ≤ (20457566906261/50000000000000 : ℝ)^29
        have hw : |(-4963647753/10000000000 : ℝ)|=(4963647753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s2_s2_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2354151077/5000000000 : ℝ)*x 0 + (338785817/625000000 : ℝ)*x 1 + (2374537313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2354151077/5000000000 : ℝ)^37 ≤ (4781124082287/12500000000000 : ℝ)^29 := by
    have hnat : (2354151077 : ℕ)^37*12500000000000^29 ≤ 4781124082287^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2354151077 5000000000 4781124082287 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338785817/625000000 : ℝ)^37 ≤ (45780271384169/100000000000000 : ℝ)^29 := by
    have hnat : (338785817 : ℕ)^37*100000000000000^29 ≤ 45780271384169^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338785817 625000000 45780271384169 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2374537313/10000000000 : ℝ)^37 ≤ (7985367967371/50000000000000 : ℝ)^29 := by
    have hnat : (2374537313 : ℕ)^37*50000000000000^29 ≤ 7985367967371^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2374537313 10000000000 7985367967371 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2354151077/5000000000 : ℝ), (338785817/625000000 : ℝ), (2374537313/10000000000 : ℝ)] ![(4781124082287/12500000000000 : ℝ), (45780271384169/100000000000000 : ℝ), (7985367967371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2354151077/5000000000 : ℝ)|^37 ≤ (4781124082287/12500000000000 : ℝ)^29
        have hw : |(2354151077/5000000000 : ℝ)|=(2354151077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338785817/625000000 : ℝ)|^37 ≤ (45780271384169/100000000000000 : ℝ)^29
        have hw : |(338785817/625000000 : ℝ)|=(338785817/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2374537313/10000000000 : ℝ)|^37 ≤ (7985367967371/50000000000000 : ℝ)^29
        have hw : |(2374537313/10000000000 : ℝ)|=(2374537313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313062_s2_s2_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6375853709/10000000000 : ℝ)*x 0 + (4669504529/10000000000 : ℝ)*x 1 + (-1079060727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6375853709/10000000000 : ℝ)^37 ≤ (28157097927727/50000000000000 : ℝ)^29 := by
    have hnat : (6375853709 : ℕ)^37*50000000000000^29 ≤ 28157097927727^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6375853709 10000000000 28157097927727 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4669504529/10000000000 : ℝ)^37 ≤ (37847322412063/100000000000000 : ℝ)^29 := by
    have hnat : (4669504529 : ℕ)^37*100000000000000^29 ≤ 37847322412063^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4669504529 10000000000 37847322412063 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079060727/10000000000 : ℝ)^37 ≤ (5838481710463/100000000000000 : ℝ)^29 := by
    have hnat : (1079060727 : ℕ)^37*100000000000000^29 ≤ 5838481710463^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079060727 10000000000 5838481710463 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6375853709/10000000000 : ℝ), (4669504529/10000000000 : ℝ), (-1079060727/10000000000 : ℝ)] ![(28157097927727/50000000000000 : ℝ), (37847322412063/100000000000000 : ℝ), (5838481710463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6375853709/10000000000 : ℝ)|^37 ≤ (28157097927727/50000000000000 : ℝ)^29
        have hw : |(6375853709/10000000000 : ℝ)|=(6375853709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4669504529/10000000000 : ℝ)|^37 ≤ (37847322412063/100000000000000 : ℝ)^29
        have hw : |(4669504529/10000000000 : ℝ)|=(4669504529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1079060727/10000000000 : ℝ)|^37 ≤ (5838481710463/100000000000000 : ℝ)^29
        have hw : |(-1079060727/10000000000 : ℝ)|=(1079060727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313062_s2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((2509/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2509/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(62841/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(62841/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-47623/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-47623/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16901/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16901/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34023/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34023/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5307/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5307/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (2509/4000 : ℝ) ^ (73/16 : ℝ) ≤ (1190756763034476573/10000000000000000000 : ℝ) := by
    have hpowers : (2509/4000 : ℝ)^73 ≤ (1190756763034476573/10000000000000000000 : ℝ)^16 := by
      have hnat : (2509 : ℕ)^73*10000000000000000000^16 ≤ 1190756763034476573^16*4000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2509 4000 1190756763034476573 10000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2509/4000 : ℝ)) (X := (1190756763034476573/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (11190756763034476573/10000000000000000000 : ℝ) ≤ (10249647317575521/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (11190756763034476573/10000000000000000000 : ℝ)^16 ≤ (10249647317575521/10000000000000000 : ℝ)^73 := by
      have hnat : (11190756763034476573 : ℕ)^16*10000000000000000^73 ≤ 10249647317575521^73*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11190756763034476573 10000000000000000000 10249647317575521 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10249647317575521/10000000000000000 : ℝ)) (X := (11190756763034476573/10000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (6190756763034476573/5000000000000000000 : ℝ) ≤ (5239670463881929/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (6190756763034476573/5000000000000000000 : ℝ)^16 ≤ (5239670463881929/5000000000000000 : ℝ)^73 := by
      have hnat : (6190756763034476573 : ℕ)^16*5000000000000000^73 ≤ 5239670463881929^73*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6190756763034476573 5000000000000000000 5239670463881929 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5239670463881929/5000000000000000 : ℝ)) (X := (6190756763034476573/5000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(249647317575521/6272500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(229693610188337/6272500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (2509/4000 : ℝ)) (alpha := (249647317575521/6272500000000000 : ℝ)) (beta := (229693610188337/6272500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2509/4000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(249647317575521/6272500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(229693610188337/6272500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (62841/100000 : ℝ) ^ (73/16 : ℝ) ≤ (48033482824395317/400000000000000000 : ℝ) := by
    have hpowers : (62841/100000 : ℝ)^73 ≤ (48033482824395317/400000000000000000 : ℝ)^16 := by
      have hnat : (62841 : ℕ)^73*400000000000000000^16 ≤ 48033482824395317^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62841 100000 48033482824395317 400000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62841/100000 : ℝ)) (X := (48033482824395317/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (448033482824395317/400000000000000000 : ℝ) ≤ (5125835093145809/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (448033482824395317/400000000000000000 : ℝ)^16 ≤ (5125835093145809/5000000000000000 : ℝ)^73 := by
      have hnat : (448033482824395317 : ℕ)^16*5000000000000000^73 ≤ 5125835093145809^73*400000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        448033482824395317 400000000000000000 5125835093145809 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5125835093145809/5000000000000000 : ℝ)) (X := (448033482824395317/400000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (248033482824395317/200000000000000000 : ℝ) ≤ (10483078462461497/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (248033482824395317/200000000000000000 : ℝ)^16 ≤ (10483078462461497/10000000000000000 : ℝ)^73 := by
      have hnat : (248033482824395317 : ℕ)^16*10000000000000000^73 ≤ 10483078462461497^73*200000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        248033482824395317 200000000000000000 10483078462461497 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10483078462461497/10000000000000000 : ℝ)) (X := (248033482824395317/200000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(41945031048603/1047350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(231408276169879/6284100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (62841/100000 : ℝ)) (alpha := (41945031048603/1047350000000000 : ℝ)) (beta := (231408276169879/6284100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (62841/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(41945031048603/1047350000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(231408276169879/6284100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (47623/100000 : ℝ) ^ (73/16 : ℝ) ≤ (3388745257837085641/100000000000000000000 : ℝ) := by
    have hpowers : (47623/100000 : ℝ)^73 ≤ (3388745257837085641/100000000000000000000 : ℝ)^16 := by
      have hnat : (47623 : ℕ)^73*100000000000000000000^16 ≤ 3388745257837085641^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47623 100000 3388745257837085641 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47623/100000 : ℝ)) (X := (3388745257837085641/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (103388745257837085641/100000000000000000000 : ℝ) ≤ (10073310535625459/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (103388745257837085641/100000000000000000000 : ℝ)^16 ≤ (10073310535625459/10000000000000000 : ℝ)^73 := by
      have hnat : (103388745257837085641 : ℕ)^16*10000000000000000^73 ≤ 10073310535625459^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103388745257837085641 100000000000000000000 10073310535625459 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10073310535625459/10000000000000000 : ℝ)) (X := (103388745257837085641/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (53388745257837085641/50000000000000000000 : ℝ) ≤ (2028953639966671/2000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (53388745257837085641/50000000000000000000 : ℝ)^16 ≤ (2028953639966671/2000000000000000 : ℝ)^73 := by
      have hnat : (53388745257837085641 : ℕ)^16*2000000000000000^73 ≤ 2028953639966671^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53388745257837085641 50000000000000000000 2028953639966671 2000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2028953639966671/2000000000000000 : ℝ)) (X := (53388745257837085641/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(73310535625459/4762300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(8932208025987/595287500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (47623/100000 : ℝ)) (alpha := (73310535625459/4762300000000000 : ℝ)) (beta := (8932208025987/595287500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (47623/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(73310535625459/4762300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(8932208025987/595287500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-469852923/2500000000 : ℝ)*X 0 0+(4905482621/10000000000 : ℝ)*X 0 1+(-5611238537/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((1226487137/2500000000 : ℝ)*X 1 0+(-1881632097/10000000000 : ℝ)*X 1 1+(-21910731/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5080219471/10000000000 : ℝ)*X 2 0+(1270186791/2500000000 : ℝ)*X 2 1+(1171716613/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1582191671/10000000000 : ℝ)*X 0 0+(2245813661/5000000000 : ℝ)*X 0 1+(-6211464493/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((977108209/2000000000 : ℝ)*X 1 0+(-655492303/5000000000 : ℝ)*X 1 1+(-753450831/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2437932191/5000000000 : ℝ)*X 2 0+(1464852577/2500000000 : ℝ)*X 2 1+(1573191871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((5161701073/10000000000 : ℝ)*X 0 0+(602819963/1000000000 : ℝ)*X 0 1+(-889682839/10000000000 : ℝ)*X 0 2+(5161701073/10000000000 : ℝ)*X 1 0+(602819963/1000000000 : ℝ)*X 1 1+(-889682839/10000000000 : ℝ)*X 1 2+(5161701073/10000000000 : ℝ)*X 2 0+(602819963/1000000000 : ℝ)*X 2 1+(-889682839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1232590633/10000000000 : ℝ)*X 0 0+(2399948877/5000000000 : ℝ)*X 0 1+(-6158873561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2293947927/5000000000 : ℝ)*X 1 0+(-10462823/62500000 : ℝ)*X 1 1+(-378697831/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((5750508787/10000000000 : ℝ)*X 2 0+(2487877013/5000000000 : ℝ)*X 2 1+(1592421309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((6245729099/10000000000 : ℝ)*X 0 0+(4929424859/10000000000 : ℝ)*X 0 1+(-446995527/5000000000 : ℝ)*X 0 2+(6245729099/10000000000 : ℝ)*X 1 0+(4929424859/10000000000 : ℝ)*X 1 1+(-446995527/5000000000 : ℝ)*X 1 2+(6245729099/10000000000 : ℝ)*X 2 0+(4929424859/10000000000 : ℝ)*X 2 1+(-446995527/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-128391273/1250000000 : ℝ)*X 0 0+(1311179069/2500000000 : ℝ)*X 0 1+(-7331411/12500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((578111111/1000000000 : ℝ)*X 1 0+(-1565286551/10000000000 : ℝ)*X 1 1+(-4963647753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2354151077/5000000000 : ℝ)*X 2 0+(338785817/625000000 : ℝ)*X 2 1+(2374537313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((6375853709/10000000000 : ℝ)*X 0 0+(4669504529/10000000000 : ℝ)*X 0 1+(-1079060727/10000000000 : ℝ)*X 0 2+(6375853709/10000000000 : ℝ)*X 1 0+(4669504529/10000000000 : ℝ)*X 1 1+(-1079060727/10000000000 : ℝ)*X 1 2+(6375853709/10000000000 : ℝ)*X 2 0+(4669504529/10000000000 : ℝ)*X 2 1+(-1079060727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313062_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((16901/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16901/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (197883140473285514066080137/11489048750000000000000000000000 : ℝ) := by norm_num
    linear_combination (107375986441/250000000000 : ℝ)*(base39) + (245548840423/1000000000000 : ℝ)*(base49) + (91591385731/500000000000 : ℝ)*(base60) + (7040331013131/1000000000000 : ℝ)*(major_s2_0) + (7040331013131/1000000000000 : ℝ)*(major_s2_1) + (7040331013131/1000000000000 : ℝ)*(major_s2_2) + (88887581/1000000000000 : ℝ)*(sp_s2_0) + (28368299/250000000000 : ℝ)*(sp_s2_1) + (1240832648803/125000000000 : ℝ)*(sp_s2_7) + (4963238374073/500000000000 : ℝ)*(sp_s2_8) + (992653287417/100000000000 : ℝ)*(sp_s2_9) + (4153906207043/1000000000000 : ℝ)*(sp_s2_13) + (159856663/1000000000000 : ℝ)*(sp_s2_15) + (43440767/200000000000 : ℝ)*(sp_s2_23) + (4153906207043/1000000000000 : ℝ)*(f.failure) + (1985350015601/200000000000 : ℝ)*(f.sum) + (52213125233992763789/99755898100000000000000000000000 : ℝ)*base62 + (1790261701551003/2381150000000000000000000000 : ℝ)*base65 + (1290589395505797/2094700000000000000000000000 : ℝ)*base66 + (296369299935241/4762300000000000000000000000 : ℝ)*base68 + (7141234429488559421/22978097500000000000000000000000 : ℝ)*base71 + (97495506057431/482500000000000000000000000 : ℝ)*base72 + (189470927044139/523675000000000000000000000 : ℝ)*base75 + (189562126721827/482500000000000000000000000 : ℝ)*base77 + (426795129710871017/2526731875000000000000000000000 : ℝ)*base79 + (3059/100000000000000000 : ℝ)*base86 + (3059/100000000000000000 : ℝ)*base88 + (3059/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34023/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34023/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (54727721110267294432024317906827/3128594354161250000000000000000000000 : ℝ) := by norm_num
    linear_combination (101063367719/250000000000 : ℝ)*(base39) + (60366876993/200000000000 : ℝ)*(base49) + (1685399/500000000000 : ℝ)*(base60) + (3590108780573/500000000000 : ℝ)*(major_s2_0) + (3590108780573/500000000000 : ℝ)*(major_s2_1) + (3590108780573/500000000000 : ℝ)*(major_s2_2) + (33413239/1000000000000 : ℝ)*(sp_s2_2) + (9392459/100000000000 : ℝ)*(sp_s2_7) + (77201747/1000000000000 : ℝ)*(sp_s2_8) + (2530973473179/250000000000 : ℝ)*(sp_s2_14) + (253097765389/25000000000 : ℝ)*(sp_s2_15) + (10123954404067/1000000000000 : ℝ)*(sp_s2_16) + (4236158470387/1000000000000 : ℝ)*(sp_s2_20) + (283003677/1000000000000 : ℝ)*(sp_s2_27) + (264777592129/62500000000 : ℝ)*(f.failure) + (5061993908653/500000000000 : ℝ)*(f.sum) + (11578304687861792837/49877949050000000000000000000000 : ℝ)*base62 + (376145054193871/1190575000000000000000000000 : ℝ)*base64 + (729257323542691/1571025000000000000000000000 : ℝ)*base67 + (384326574830877/595287500000000000000000000 : ℝ)*base68 + (31190321936329929641/149357633750000000000000000000000 : ℝ)*base70 + (765918987797113/1568125000000000000000000000 : ℝ)*base73 + (136453069000451/523675000000000000000000000 : ℝ)*base74 + (631963285288467/3136250000000000000000000000 : ℝ)*base76 + (21076182773929311629/49271271562500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (5323/6250000000000000 : ℝ)*base87 + (5323/6250000000000000 : ℝ)*base89 + (5323/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5307/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5307/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10304215059604918402009983540347/3128594354161250000000000000000000000 : ℝ) := by norm_num
    linear_combination (2005363/1000000000000 : ℝ)*(base11) + (923744515553/1000000000000 : ℝ)*(base39) + (351473/1000000000000 : ℝ)*(base40) + (100022439081/500000000000 : ℝ)*(base49) + (5684436710281/1000000000000 : ℝ)*(major_s2_0) + (5684436710281/1000000000000 : ℝ)*(major_s2_1) + (5684436710281/1000000000000 : ℝ)*(major_s2_2) + (4889263/500000000000 : ℝ)*(sp_s2_0) + (535393/25000000000 : ℝ)*(sp_s2_2) + (25536789/1000000000000 : ℝ)*(sp_s2_9) + (4007476665213/500000000000 : ℝ)*(sp_s2_21) + (1602993022863/200000000000 : ℝ)*(sp_s2_22) + (4007459080903/500000000000 : ℝ)*(sp_s2_23) + (838476802097/250000000000 : ℝ)*(sp_s2_27) + (838476802097/250000000000 : ℝ)*(f.failure) + (1602993022863/200000000000 : ℝ)*(f.sum) + (21431731656353060131/99755898100000000000000000000000 : ℝ)*base63 + (78961958731061/1190575000000000000000000000 : ℝ)*base64 + (3977495828458579/6284100000000000000000000000 : ℝ)*base67 + (113952939781319/4762300000000000000000000000 : ℝ)*base69 + (53279700736513192827/298715267500000000000000000000000 : ℝ)*base70 + (5130450773677447/6272500000000000000000000000 : ℝ)*base73 + (5887931521953/1047350000000000000000000000 : ℝ)*base75 + (2369629482214599/6272500000000000000000000000 : ℝ)*base76 + (197253118782180313601/197085086250000000000000000000000 : ℝ)*base79 + (10761/25000000000000000 : ℝ)*base86 + (10761/25000000000000000 : ℝ)*base88 + (10761/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((2509/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2509/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(62841/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(62841/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-47623/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-47623/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16901/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16901/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34023/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34023/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5307/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5307/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313062_s2 p hpa hpb X hX hprev1

#print axioms solution

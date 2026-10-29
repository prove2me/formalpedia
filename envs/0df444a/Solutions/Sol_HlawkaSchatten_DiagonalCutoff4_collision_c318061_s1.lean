-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c318061_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:24:32.187411+00:00
-- url     : https://prove2.me/submissions/d8717033-f414-406c-aef2-9f0d1e5b6df5

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
theorem collision_support_c318061_s1_s1_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1660623083/10000000000 : ℝ)*x 0 + (4511787299/10000000000 : ℝ)*x 1 + (239687387/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1660623083/10000000000 : ℝ)^79 ≤ (10525547017927/100000000000000 : ℝ)^63 := by
    have hnat : (1660623083 : ℕ)^79*100000000000000^63 ≤ 10525547017927^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1660623083 10000000000 10525547017927 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4511787299/10000000000 : ℝ)^79 ≤ (2303796724913/6250000000000 : ℝ)^63 := by
    have hnat : (4511787299 : ℕ)^79*6250000000000^63 ≤ 2303796724913^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511787299 10000000000 2303796724913 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239687387/400000000 : ℝ)^79 ≤ (52613705371741/100000000000000 : ℝ)^63 := by
    have hnat : (239687387 : ℕ)^79*100000000000000^63 ≤ 52613705371741^63*400000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239687387 400000000 52613705371741 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1660623083/10000000000 : ℝ), (4511787299/10000000000 : ℝ), (239687387/400000000 : ℝ)] ![(10525547017927/100000000000000 : ℝ), (2303796724913/6250000000000 : ℝ), (52613705371741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1660623083/10000000000 : ℝ)|^79 ≤ (10525547017927/100000000000000 : ℝ)^63
        have hw : |(-1660623083/10000000000 : ℝ)|=(1660623083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4511787299/10000000000 : ℝ)|^79 ≤ (2303796724913/6250000000000 : ℝ)^63
        have hw : |(4511787299/10000000000 : ℝ)|=(4511787299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(239687387/400000000 : ℝ)|^79 ≤ (52613705371741/100000000000000 : ℝ)^63
        have hw : |(239687387/400000000 : ℝ)|=(239687387/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318061_s1_s1_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (234645327/500000000 : ℝ)*x 0 + (-822354393/5000000000 : ℝ)*x 1 + (2916873391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (234645327/500000000 : ℝ)^79 ≤ (1549025513459/4000000000000 : ℝ)^63 := by
    have hnat : (234645327 : ℕ)^79*4000000000000^63 ≤ 1549025513459^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234645327 500000000 1549025513459 4000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (822354393/5000000000 : ℝ)^79 ≤ (10399213813713/100000000000000 : ℝ)^63 := by
    have hnat : (822354393 : ℕ)^79*100000000000000^63 ≤ 10399213813713^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      822354393 5000000000 10399213813713 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2916873391/5000000000 : ℝ)^79 ≤ (12718787082301/25000000000000 : ℝ)^63 := by
    have hnat : (2916873391 : ℕ)^79*25000000000000^63 ≤ 12718787082301^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2916873391 5000000000 12718787082301 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(234645327/500000000 : ℝ), (-822354393/5000000000 : ℝ), (2916873391/5000000000 : ℝ)] ![(1549025513459/4000000000000 : ℝ), (10399213813713/100000000000000 : ℝ), (12718787082301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(234645327/500000000 : ℝ)|^79 ≤ (1549025513459/4000000000000 : ℝ)^63
        have hw : |(234645327/500000000 : ℝ)|=(234645327/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-822354393/5000000000 : ℝ)|^79 ≤ (10399213813713/100000000000000 : ℝ)^63
        have hw : |(-822354393/5000000000 : ℝ)|=(822354393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2916873391/5000000000 : ℝ)|^79 ≤ (12718787082301/25000000000000 : ℝ)^63
        have hw : |(2916873391/5000000000 : ℝ)|=(2916873391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318061_s1_s1_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4766507091/10000000000 : ℝ)*x 0 + (402985069/625000000 : ℝ)*x 1 + (-583221453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4766507091/10000000000 : ℝ)^79 ≤ (7897748810771/20000000000000 : ℝ)^63 := by
    have hnat : (4766507091 : ℕ)^79*20000000000000^63 ≤ 7897748810771^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4766507091 10000000000 7897748810771 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402985069/625000000 : ℝ)^79 ≤ (1441932290523/2500000000000 : ℝ)^63 := by
    have hnat : (402985069 : ℕ)^79*2500000000000^63 ≤ 1441932290523^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402985069 625000000 1441932290523 2500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (583221453/10000000000 : ℝ)^79 ≤ (708491078197/25000000000000 : ℝ)^63 := by
    have hnat : (583221453 : ℕ)^79*25000000000000^63 ≤ 708491078197^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583221453 10000000000 708491078197 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4766507091/10000000000 : ℝ), (402985069/625000000 : ℝ), (-583221453/10000000000 : ℝ)] ![(7897748810771/20000000000000 : ℝ), (1441932290523/2500000000000 : ℝ), (708491078197/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4766507091/10000000000 : ℝ)|^79 ≤ (7897748810771/20000000000000 : ℝ)^63
        have hw : |(4766507091/10000000000 : ℝ)|=(4766507091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(402985069/625000000 : ℝ)|^79 ≤ (1441932290523/2500000000000 : ℝ)^63
        have hw : |(402985069/625000000 : ℝ)|=(402985069/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-583221453/10000000000 : ℝ)|^79 ≤ (708491078197/25000000000000 : ℝ)^63
        have hw : |(-583221453/10000000000 : ℝ)|=(583221453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318061_s1_s1_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3279703369/5000000000 : ℝ)*x 0 + (2563827751/10000000000 : ℝ)*x 1 + (617811079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3279703369/5000000000 : ℝ)^79 ≤ (58932379124587/100000000000000 : ℝ)^63 := by
    have hnat : (3279703369 : ℕ)^79*100000000000000^63 ≤ 58932379124587^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3279703369 5000000000 58932379124587 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2563827751/10000000000 : ℝ)^79 ≤ (1134084443641/6250000000000 : ℝ)^63 := by
    have hnat : (2563827751 : ℕ)^79*6250000000000^63 ≤ 1134084443641^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563827751 10000000000 1134084443641 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (617811079/2000000000 : ℝ)^79 ≤ (22922269766733/100000000000000 : ℝ)^63 := by
    have hnat : (617811079 : ℕ)^79*100000000000000^63 ≤ 22922269766733^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617811079 2000000000 22922269766733 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3279703369/5000000000 : ℝ), (2563827751/10000000000 : ℝ), (617811079/2000000000 : ℝ)] ![(58932379124587/100000000000000 : ℝ), (1134084443641/6250000000000 : ℝ), (22922269766733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3279703369/5000000000 : ℝ)|^79 ≤ (58932379124587/100000000000000 : ℝ)^63
        have hw : |(3279703369/5000000000 : ℝ)|=(3279703369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2563827751/10000000000 : ℝ)|^79 ≤ (1134084443641/6250000000000 : ℝ)^63
        have hw : |(2563827751/10000000000 : ℝ)|=(2563827751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(617811079/2000000000 : ℝ)|^79 ≤ (22922269766733/100000000000000 : ℝ)^63
        have hw : |(617811079/2000000000 : ℝ)|=(617811079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318061_s1_s1_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-427940373/2500000000 : ℝ)*x 0 + (741836909/2000000000 : ℝ)*x 1 + (6674639301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427940373/2500000000 : ℝ)^79 ≤ (5466787311443/50000000000000 : ℝ)^63 := by
    have hnat : (427940373 : ℕ)^79*50000000000000^63 ≤ 5466787311443^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427940373 2500000000 5466787311443 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (741836909/2000000000 : ℝ)^79 ≤ (230663472823/800000000000 : ℝ)^63 := by
    have hnat : (741836909 : ℕ)^79*800000000000^63 ≤ 230663472823^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741836909 2000000000 230663472823 800000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6674639301/10000000000 : ℝ)^79 ≤ (30116745631921/50000000000000 : ℝ)^63 := by
    have hnat : (6674639301 : ℕ)^79*50000000000000^63 ≤ 30116745631921^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6674639301 10000000000 30116745631921 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427940373/2500000000 : ℝ), (741836909/2000000000 : ℝ), (6674639301/10000000000 : ℝ)] ![(5466787311443/50000000000000 : ℝ), (230663472823/800000000000 : ℝ), (30116745631921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427940373/2500000000 : ℝ)|^79 ≤ (5466787311443/50000000000000 : ℝ)^63
        have hw : |(-427940373/2500000000 : ℝ)|=(427940373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(741836909/2000000000 : ℝ)|^79 ≤ (230663472823/800000000000 : ℝ)^63
        have hw : |(741836909/2000000000 : ℝ)|=(741836909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6674639301/10000000000 : ℝ)|^79 ≤ (30116745631921/50000000000000 : ℝ)^63
        have hw : |(6674639301/10000000000 : ℝ)|=(6674639301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318061_s1_s1_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (163703407/400000000 : ℝ)*x 0 + (-1194461647/10000000000 : ℝ)*x 1 + (6691016919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163703407/400000000 : ℝ)^79 ≤ (32618010398981/100000000000000 : ℝ)^63 := by
    have hnat : (163703407 : ℕ)^79*100000000000000^63 ≤ 32618010398981^63*400000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163703407 400000000 32618010398981 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1194461647/10000000000 : ℝ)^79 ≤ (3481554926777/50000000000000 : ℝ)^63 := by
    have hnat : (1194461647 : ℕ)^79*50000000000000^63 ≤ 3481554926777^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194461647 10000000000 3481554926777 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6691016919/10000000000 : ℝ)^79 ≤ (30209439868807/50000000000000 : ℝ)^63 := by
    have hnat : (6691016919 : ℕ)^79*50000000000000^63 ≤ 30209439868807^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6691016919 10000000000 30209439868807 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(163703407/400000000 : ℝ), (-1194461647/10000000000 : ℝ), (6691016919/10000000000 : ℝ)] ![(32618010398981/100000000000000 : ℝ), (3481554926777/50000000000000 : ℝ), (30209439868807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(163703407/400000000 : ℝ)|^79 ≤ (32618010398981/100000000000000 : ℝ)^63
        have hw : |(163703407/400000000 : ℝ)|=(163703407/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1194461647/10000000000 : ℝ)|^79 ≤ (3481554926777/50000000000000 : ℝ)^63
        have hw : |(-1194461647/10000000000 : ℝ)|=(1194461647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6691016919/10000000000 : ℝ)|^79 ≤ (30209439868807/50000000000000 : ℝ)^63
        have hw : |(6691016919/10000000000 : ℝ)|=(6691016919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318061_s1_s1_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4169385597/10000000000 : ℝ)*x 0 + (723193163/1000000000 : ℝ)*x 1 + (-4982859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169385597/10000000000 : ℝ)^79 ≤ (16693693329227/50000000000000 : ℝ)^63 := by
    have hnat : (4169385597 : ℕ)^79*50000000000000^63 ≤ 16693693329227^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169385597 10000000000 16693693329227 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (723193163/1000000000 : ℝ)^79 ≤ (66605389907003/100000000000000 : ℝ)^63 := by
    have hnat : (723193163 : ℕ)^79*100000000000000^63 ≤ 66605389907003^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723193163 1000000000 66605389907003 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4982859/10000000000 : ℝ)^79 ≤ (3611711137/50000000000000 : ℝ)^63 := by
    have hnat : (4982859 : ℕ)^79*50000000000000^63 ≤ 3611711137^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4982859 10000000000 3611711137 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169385597/10000000000 : ℝ), (723193163/1000000000 : ℝ), (-4982859/10000000000 : ℝ)] ![(16693693329227/50000000000000 : ℝ), (66605389907003/100000000000000 : ℝ), (3611711137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169385597/10000000000 : ℝ)|^79 ≤ (16693693329227/50000000000000 : ℝ)^63
        have hw : |(4169385597/10000000000 : ℝ)|=(4169385597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(723193163/1000000000 : ℝ)|^79 ≤ (66605389907003/100000000000000 : ℝ)^63
        have hw : |(723193163/1000000000 : ℝ)|=(723193163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4982859/10000000000 : ℝ)|^79 ≤ (3611711137/50000000000000 : ℝ)^63
        have hw : |(-4982859/10000000000 : ℝ)|=(4982859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318061_s1_s1_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5798083907/10000000000 : ℝ)*x 0 + (1155801597/2500000000 : ℝ)*x 1 + (1783201789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5798083907/10000000000 : ℝ)^79 ≤ (12621363692451/25000000000000 : ℝ)^63 := by
    have hnat : (5798083907 : ℕ)^79*25000000000000^63 ≤ 12621363692451^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5798083907 10000000000 12621363692451 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1155801597/2500000000 : ℝ)^79 ≤ (38005767896751/100000000000000 : ℝ)^63 := by
    have hnat : (1155801597 : ℕ)^79*100000000000000^63 ≤ 38005767896751^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155801597 2500000000 38005767896751 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1783201789/10000000000 : ℝ)^79 ≤ (11508777326491/100000000000000 : ℝ)^63 := by
    have hnat : (1783201789 : ℕ)^79*100000000000000^63 ≤ 11508777326491^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783201789 10000000000 11508777326491 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5798083907/10000000000 : ℝ), (1155801597/2500000000 : ℝ), (1783201789/10000000000 : ℝ)] ![(12621363692451/25000000000000 : ℝ), (38005767896751/100000000000000 : ℝ), (11508777326491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5798083907/10000000000 : ℝ)|^79 ≤ (12621363692451/25000000000000 : ℝ)^63
        have hw : |(5798083907/10000000000 : ℝ)|=(5798083907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1155801597/2500000000 : ℝ)|^79 ≤ (38005767896751/100000000000000 : ℝ)^63
        have hw : |(1155801597/2500000000 : ℝ)|=(1155801597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1783201789/10000000000 : ℝ)|^79 ≤ (11508777326491/100000000000000 : ℝ)^63
        have hw : |(1783201789/10000000000 : ℝ)|=(1783201789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318061_s1_s1_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-140886061/2000000000 : ℝ)*x 0 + (4044573299/10000000000 : ℝ)*x 1 + (1405797739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140886061/2000000000 : ℝ)^79 ≤ (897770801291/25000000000000 : ℝ)^63 := by
    have hnat : (140886061 : ℕ)^79*25000000000000^63 ≤ 897770801291^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140886061 2000000000 897770801291 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4044573299/10000000000 : ℝ)^79 ≤ (32138888959879/100000000000000 : ℝ)^63 := by
    have hnat : (4044573299 : ℕ)^79*100000000000000^63 ≤ 32138888959879^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4044573299 10000000000 32138888959879 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1405797739/2000000000 : ℝ)^79 ≤ (6427002782807/10000000000000 : ℝ)^63 := by
    have hnat : (1405797739 : ℕ)^79*10000000000000^63 ≤ 6427002782807^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405797739 2000000000 6427002782807 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-140886061/2000000000 : ℝ), (4044573299/10000000000 : ℝ), (1405797739/2000000000 : ℝ)] ![(897770801291/25000000000000 : ℝ), (32138888959879/100000000000000 : ℝ), (6427002782807/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-140886061/2000000000 : ℝ)|^79 ≤ (897770801291/25000000000000 : ℝ)^63
        have hw : |(-140886061/2000000000 : ℝ)|=(140886061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4044573299/10000000000 : ℝ)|^79 ≤ (32138888959879/100000000000000 : ℝ)^63
        have hw : |(4044573299/10000000000 : ℝ)|=(4044573299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1405797739/2000000000 : ℝ)|^79 ≤ (6427002782807/10000000000000 : ℝ)^63
        have hw : |(1405797739/2000000000 : ℝ)|=(1405797739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318061_s1_s1_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (435710407/1250000000 : ℝ)*x 0 + (-144743203/1000000000 : ℝ)*x 1 + (704634411/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435710407/1250000000 : ℝ)^79 ≤ (26671263037383/100000000000000 : ℝ)^63 := by
    have hnat : (435710407 : ℕ)^79*100000000000000^63 ≤ 26671263037383^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435710407 1250000000 26671263037383 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (144743203/1000000000 : ℝ)^79 ≤ (1771930809829/20000000000000 : ℝ)^63 := by
    have hnat : (144743203 : ℕ)^79*20000000000000^63 ≤ 1771930809829^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144743203 1000000000 1771930809829 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (704634411/1000000000 : ℝ)^79 ≤ (16117270725391/25000000000000 : ℝ)^63 := by
    have hnat : (704634411 : ℕ)^79*25000000000000^63 ≤ 16117270725391^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704634411 1000000000 16117270725391 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435710407/1250000000 : ℝ), (-144743203/1000000000 : ℝ), (704634411/1000000000 : ℝ)] ![(26671263037383/100000000000000 : ℝ), (1771930809829/20000000000000 : ℝ), (16117270725391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435710407/1250000000 : ℝ)|^79 ≤ (26671263037383/100000000000000 : ℝ)^63
        have hw : |(435710407/1250000000 : ℝ)|=(435710407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-144743203/1000000000 : ℝ)|^79 ≤ (1771930809829/20000000000000 : ℝ)^63
        have hw : |(-144743203/1000000000 : ℝ)|=(144743203/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(704634411/1000000000 : ℝ)|^79 ≤ (16117270725391/25000000000000 : ℝ)^63
        have hw : |(704634411/1000000000 : ℝ)|=(704634411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318061_s1_s1_16 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6402726501/10000000000 : ℝ)*x 0 + (1268255309/2500000000 : ℝ)*x 1 + (-49575251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6402726501/10000000000 : ℝ)^79 ≤ (28586290309353/50000000000000 : ℝ)^63 := by
    have hnat : (6402726501 : ℕ)^79*50000000000000^63 ≤ 28586290309353^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6402726501 10000000000 28586290309353 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1268255309/2500000000 : ℝ)^79 ≤ (21349306788277/50000000000000 : ℝ)^63 := by
    have hnat : (1268255309 : ℕ)^79*50000000000000^63 ≤ 21349306788277^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268255309 2500000000 21349306788277 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49575251/10000000000 : ℝ)^79 ≤ (64402893877/50000000000000 : ℝ)^63 := by
    have hnat : (49575251 : ℕ)^79*50000000000000^63 ≤ 64402893877^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49575251 10000000000 64402893877 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6402726501/10000000000 : ℝ), (1268255309/2500000000 : ℝ), (-49575251/10000000000 : ℝ)] ![(28586290309353/50000000000000 : ℝ), (21349306788277/50000000000000 : ℝ), (64402893877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6402726501/10000000000 : ℝ)|^79 ≤ (28586290309353/50000000000000 : ℝ)^63
        have hw : |(6402726501/10000000000 : ℝ)|=(6402726501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1268255309/2500000000 : ℝ)|^79 ≤ (21349306788277/50000000000000 : ℝ)^63
        have hw : |(1268255309/2500000000 : ℝ)|=(1268255309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49575251/10000000000 : ℝ)|^79 ≤ (64402893877/50000000000000 : ℝ)^63
        have hw : |(-49575251/10000000000 : ℝ)|=(49575251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318061_s1_s1_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3889258819/5000000000 : ℝ)*x 0 + (2492101261/10000000000 : ℝ)*x 1 + (1531753871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3889258819/5000000000 : ℝ)^79 ≤ (72977352192429/100000000000000 : ℝ)^63 := by
    have hnat : (3889258819 : ℕ)^79*100000000000000^63 ≤ 72977352192429^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3889258819 5000000000 72977352192429 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2492101261/10000000000 : ℝ)^79 ≤ (4377765901721/25000000000000 : ℝ)^63 := by
    have hnat : (2492101261 : ℕ)^79*25000000000000^63 ≤ 4377765901721^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2492101261 10000000000 4377765901721 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1531753871/10000000000 : ℝ)^79 ≤ (4755792092839/50000000000000 : ℝ)^63 := by
    have hnat : (1531753871 : ℕ)^79*50000000000000^63 ≤ 4755792092839^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1531753871 10000000000 4755792092839 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3889258819/5000000000 : ℝ), (2492101261/10000000000 : ℝ), (1531753871/10000000000 : ℝ)] ![(72977352192429/100000000000000 : ℝ), (4377765901721/25000000000000 : ℝ), (4755792092839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3889258819/5000000000 : ℝ)|^79 ≤ (72977352192429/100000000000000 : ℝ)^63
        have hw : |(3889258819/5000000000 : ℝ)|=(3889258819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2492101261/10000000000 : ℝ)|^79 ≤ (4377765901721/25000000000000 : ℝ)^63
        have hw : |(2492101261/10000000000 : ℝ)|=(2492101261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1531753871/10000000000 : ℝ)|^79 ≤ (4755792092839/50000000000000 : ℝ)^63
        have hw : |(1531753871/10000000000 : ℝ)|=(1531753871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318061_s1_s1_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-535705903/10000000000 : ℝ)*x 0 + (1415878299/2500000000 : ℝ)*x 1 + (2804614611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535705903/10000000000 : ℝ)^79 ≤ (2547499439879/100000000000000 : ℝ)^63 := by
    have hnat : (535705903 : ℕ)^79*100000000000000^63 ≤ 2547499439879^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535705903 10000000000 2547499439879 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1415878299/2500000000 : ℝ)^79 ≤ (49020482108521/100000000000000 : ℝ)^63 := by
    have hnat : (1415878299 : ℕ)^79*100000000000000^63 ≤ 49020482108521^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415878299 2500000000 49020482108521 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2804614611/5000000000 : ℝ)^79 ≤ (24216009218071/50000000000000 : ℝ)^63 := by
    have hnat : (2804614611 : ℕ)^79*50000000000000^63 ≤ 24216009218071^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2804614611 5000000000 24216009218071 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535705903/10000000000 : ℝ), (1415878299/2500000000 : ℝ), (2804614611/5000000000 : ℝ)] ![(2547499439879/100000000000000 : ℝ), (49020482108521/100000000000000 : ℝ), (24216009218071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535705903/10000000000 : ℝ)|^79 ≤ (2547499439879/100000000000000 : ℝ)^63
        have hw : |(-535705903/10000000000 : ℝ)|=(535705903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1415878299/2500000000 : ℝ)|^79 ≤ (49020482108521/100000000000000 : ℝ)^63
        have hw : |(1415878299/2500000000 : ℝ)|=(1415878299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2804614611/5000000000 : ℝ)|^79 ≤ (24216009218071/50000000000000 : ℝ)^63
        have hw : |(2804614611/5000000000 : ℝ)|=(2804614611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318061_s1_s1_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6188144527/10000000000 : ℝ)*x 0 + (-7820371/156250000 : ℝ)*x 1 + (127256079/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6188144527/10000000000 : ℝ)^79 ≤ (54780175502051/100000000000000 : ℝ)^63 := by
    have hnat : (6188144527 : ℕ)^79*100000000000000^63 ≤ 54780175502051^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6188144527 10000000000 54780175502051 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7820371/156250000 : ℝ)^79 ≤ (116968275093/5000000000000 : ℝ)^63 := by
    have hnat : (7820371 : ℕ)^79*5000000000000^63 ≤ 116968275093^63*156250000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7820371 156250000 116968275093 5000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127256079/250000000 : ℝ)^79 ≤ (42880458978433/100000000000000 : ℝ)^63 := by
    have hnat : (127256079 : ℕ)^79*100000000000000^63 ≤ 42880458978433^63*250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127256079 250000000 42880458978433 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6188144527/10000000000 : ℝ), (-7820371/156250000 : ℝ), (127256079/250000000 : ℝ)] ![(54780175502051/100000000000000 : ℝ), (116968275093/5000000000000 : ℝ), (42880458978433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6188144527/10000000000 : ℝ)|^79 ≤ (54780175502051/100000000000000 : ℝ)^63
        have hw : |(6188144527/10000000000 : ℝ)|=(6188144527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7820371/156250000 : ℝ)|^79 ≤ (116968275093/5000000000000 : ℝ)^63
        have hw : |(-7820371/156250000 : ℝ)|=(7820371/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(127256079/250000000 : ℝ)|^79 ≤ (42880458978433/100000000000000 : ℝ)^63
        have hw : |(127256079/250000000 : ℝ)|=(127256079/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318061_s1_s1_23 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3670548423/10000000000 : ℝ)*x 0 + (3739505427/5000000000 : ℝ)*x 1 + (-454334491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3670548423/10000000000 : ℝ)^79 ≤ (5691364947823/20000000000000 : ℝ)^63 := by
    have hnat : (3670548423 : ℕ)^79*20000000000000^63 ≤ 5691364947823^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3670548423 10000000000 5691364947823 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3739505427/5000000000 : ℝ)^79 ≤ (69471165658607/100000000000000 : ℝ)^63 := by
    have hnat : (3739505427 : ℕ)^79*100000000000000^63 ≤ 69471165658607^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3739505427 5000000000 69471165658607 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454334491/10000000000 : ℝ)^79 ≤ (518002396697/25000000000000 : ℝ)^63 := by
    have hnat : (454334491 : ℕ)^79*25000000000000^63 ≤ 518002396697^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454334491 10000000000 518002396697 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3670548423/10000000000 : ℝ), (3739505427/5000000000 : ℝ), (-454334491/10000000000 : ℝ)] ![(5691364947823/20000000000000 : ℝ), (69471165658607/100000000000000 : ℝ), (518002396697/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3670548423/10000000000 : ℝ)|^79 ≤ (5691364947823/20000000000000 : ℝ)^63
        have hw : |(3670548423/10000000000 : ℝ)|=(3670548423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3739505427/5000000000 : ℝ)|^79 ≤ (69471165658607/100000000000000 : ℝ)^63
        have hw : |(3739505427/5000000000 : ℝ)|=(3739505427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-454334491/10000000000 : ℝ)|^79 ≤ (518002396697/25000000000000 : ℝ)^63
        have hw : |(-454334491/10000000000 : ℝ)|=(454334491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318061_s1_s1_27 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1696719659/2000000000 : ℝ)*x 0 + (1510584327/10000000000 : ℝ)*x 1 + (1502867963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1696719659/2000000000 : ℝ)^79 ≤ (81365764221159/100000000000000 : ℝ)^63 := by
    have hnat : (1696719659 : ℕ)^79*100000000000000^63 ≤ 81365764221159^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696719659 2000000000 81365764221159 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1510584327/10000000000 : ℝ)^79 ≤ (9347034738601/100000000000000 : ℝ)^63 := by
    have hnat : (1510584327 : ℕ)^79*100000000000000^63 ≤ 9347034738601^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510584327 10000000000 9347034738601 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1502867963/10000000000 : ℝ)^79 ≤ (9287201023303/100000000000000 : ℝ)^63 := by
    have hnat : (1502867963 : ℕ)^79*100000000000000^63 ≤ 9287201023303^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1502867963 10000000000 9287201023303 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1696719659/2000000000 : ℝ), (1510584327/10000000000 : ℝ), (1502867963/10000000000 : ℝ)] ![(81365764221159/100000000000000 : ℝ), (9347034738601/100000000000000 : ℝ), (9287201023303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1696719659/2000000000 : ℝ)|^79 ≤ (81365764221159/100000000000000 : ℝ)^63
        have hw : |(1696719659/2000000000 : ℝ)|=(1696719659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1510584327/10000000000 : ℝ)|^79 ≤ (9347034738601/100000000000000 : ℝ)^63
        have hw : |(1510584327/10000000000 : ℝ)|=(1510584327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1502867963/10000000000 : ℝ)|^79 ≤ (9287201023303/100000000000000 : ℝ)^63
        have hw : |(1502867963/10000000000 : ℝ)|=(1502867963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318061_s1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((9569/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9569/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75397/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75397/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35709/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35709/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((48493/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48493/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13299/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13299/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48023/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48023/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (34269/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (9569/12500 : ℝ) ^ (39/8 : ℝ) ≤ (13591210676922295571/50000000000000000000 : ℝ) := by
    have hpowers : (9569/12500 : ℝ)^39 ≤ (13591210676922295571/50000000000000000000 : ℝ)^8 := by
      have hnat : (9569 : ℕ)^39*50000000000000000000^8 ≤ 13591210676922295571^8*12500^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9569 12500 13591210676922295571 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9569/12500 : ℝ)) (X := (13591210676922295571/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (63591210676922295571/50000000000000000000 : ℝ) ≤ (2626400485533887/2500000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (63591210676922295571/50000000000000000000 : ℝ)^8 ≤ (2626400485533887/2500000000000000 : ℝ)^39 := by
      have hnat : (63591210676922295571 : ℕ)^8*2500000000000000^39 ≤ 2626400485533887^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63591210676922295571 50000000000000000000 2626400485533887 2500000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2626400485533887/2500000000000000 : ℝ)) (X := (63591210676922295571/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (38591210676922295571/25000000000000000000 : ℝ) ≤ (2668803790721/2441406250000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (38591210676922295571/25000000000000000000 : ℝ)^8 ≤ (2668803790721/2441406250000 : ℝ)^39 := by
      have hnat : (38591210676922295571 : ℕ)^8*2441406250000^39 ≤ 2668803790721^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38591210676922295571 25000000000000000000 2668803790721 2441406250000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2668803790721/2441406250000 : ℝ)) (X := (38591210676922295571/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(126400485533887/1913800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(106454596164417/1913800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (9569/12500 : ℝ)) (alpha := (126400485533887/1913800000000000 : ℝ)) (beta := (106454596164417/1913800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (9569/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(126400485533887/1913800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(106454596164417/1913800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (75397/100000 : ℝ) ^ (39/8 : ℝ) ≤ (12620340592397113849/50000000000000000000 : ℝ) := by
    have hpowers : (75397/100000 : ℝ)^39 ≤ (12620340592397113849/50000000000000000000 : ℝ)^8 := by
      have hnat : (75397 : ℕ)^39*50000000000000000000^8 ≤ 12620340592397113849^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75397 100000 12620340592397113849 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75397/100000 : ℝ)) (X := (12620340592397113849/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (62620340592397113849/50000000000000000000 : ℝ) ≤ (5236249683538587/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (62620340592397113849/50000000000000000000 : ℝ)^8 ≤ (5236249683538587/5000000000000000 : ℝ)^39 := by
      have hnat : (62620340592397113849 : ℕ)^8*5000000000000000^39 ≤ 5236249683538587^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62620340592397113849 50000000000000000000 5236249683538587 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5236249683538587/5000000000000000 : ℝ)) (X := (62620340592397113849/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (37620340592397113849/25000000000000000000 : ℝ) ≤ (3398261007551/3125000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (37620340592397113849/25000000000000000000 : ℝ)^8 ≤ (3398261007551/3125000000000 : ℝ)^39 := by
      have hnat : (37620340592397113849 : ℕ)^8*3125000000000^39 ≤ 3398261007551^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37620340592397113849 25000000000000000000 3398261007551 3125000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3398261007551/3125000000000 : ℝ)) (X := (37620340592397113849/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(236249683538587/3769850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(200967928543013/3769850000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (75397/100000 : ℝ)) (alpha := (236249683538587/3769850000000000 : ℝ)) (beta := (200967928543013/3769850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (75397/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(236249683538587/3769850000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(200967928543013/3769850000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (35709/50000 : ℝ) ^ (39/8 : ℝ) ≤ (19378156518687485199/100000000000000000000 : ℝ) := by
    have hpowers : (35709/50000 : ℝ)^39 ≤ (19378156518687485199/100000000000000000000 : ℝ)^8 := by
      have hnat : (35709 : ℕ)^39*100000000000000000000^8 ≤ 19378156518687485199^8*50000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35709 50000 19378156518687485199 100000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35709/50000 : ℝ)) (X := (19378156518687485199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (119378156518687485199/100000000000000000000 : ℝ) ≤ (2074003360701071/2000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (119378156518687485199/100000000000000000000 : ℝ)^8 ≤ (2074003360701071/2000000000000000 : ℝ)^39 := by
      have hnat : (119378156518687485199 : ℕ)^8*2000000000000000^39 ≤ 2074003360701071^39*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        119378156518687485199 100000000000000000000 2074003360701071 2000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2074003360701071/2000000000000000 : ℝ)) (X := (119378156518687485199/100000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (69378156518687485199/50000000000000000000 : ℝ) ≤ (10694981842566067/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (69378156518687485199/50000000000000000000 : ℝ)^8 ≤ (10694981842566067/10000000000000000 : ℝ)^39 := by
      have hnat : (69378156518687485199 : ℕ)^8*10000000000000000^39 ≤ 10694981842566067^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69378156518687485199 50000000000000000000 10694981842566067 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10694981842566067/10000000000000000 : ℝ)) (X := (69378156518687485199/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(24667786900357/476120000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(13540209960863/297575000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (35709/50000 : ℝ)) (alpha := (24667786900357/476120000000000 : ℝ)) (beta := (13540209960863/297575000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (35709/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(24667786900357/476120000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(13540209960863/297575000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1660623083/10000000000 : ℝ)*X 0 0+(4511787299/10000000000 : ℝ)*X 0 1+(239687387/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((234645327/500000000 : ℝ)*X 1 0+(-822354393/5000000000 : ℝ)*X 1 1+(2916873391/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4766507091/10000000000 : ℝ)*X 2 0+(402985069/625000000 : ℝ)*X 2 1+(-583221453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3279703369/5000000000 : ℝ)*X 0 0+(2563827751/10000000000 : ℝ)*X 0 1+(617811079/2000000000 : ℝ)*X 0 2+(3279703369/5000000000 : ℝ)*X 1 0+(2563827751/10000000000 : ℝ)*X 1 1+(617811079/2000000000 : ℝ)*X 1 2+(3279703369/5000000000 : ℝ)*X 2 0+(2563827751/10000000000 : ℝ)*X 2 1+(617811079/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-427940373/2500000000 : ℝ)*X 0 0+(741836909/2000000000 : ℝ)*X 0 1+(6674639301/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((163703407/400000000 : ℝ)*X 1 0+(-1194461647/10000000000 : ℝ)*X 1 1+(6691016919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4169385597/10000000000 : ℝ)*X 2 0+(723193163/1000000000 : ℝ)*X 2 1+(-4982859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((5798083907/10000000000 : ℝ)*X 0 0+(1155801597/2500000000 : ℝ)*X 0 1+(1783201789/10000000000 : ℝ)*X 0 2+(5798083907/10000000000 : ℝ)*X 1 0+(1155801597/2500000000 : ℝ)*X 1 1+(1783201789/10000000000 : ℝ)*X 1 2+(5798083907/10000000000 : ℝ)*X 2 0+(1155801597/2500000000 : ℝ)*X 2 1+(1783201789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-140886061/2000000000 : ℝ)*X 0 0+(4044573299/10000000000 : ℝ)*X 0 1+(1405797739/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((435710407/1250000000 : ℝ)*X 1 0+(-144743203/1000000000 : ℝ)*X 1 1+(704634411/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6402726501/10000000000 : ℝ)*X 2 0+(1268255309/2500000000 : ℝ)*X 2 1+(-49575251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3889258819/5000000000 : ℝ)*X 0 0+(2492101261/10000000000 : ℝ)*X 0 1+(1531753871/10000000000 : ℝ)*X 0 2+(3889258819/5000000000 : ℝ)*X 1 0+(2492101261/10000000000 : ℝ)*X 1 1+(1531753871/10000000000 : ℝ)*X 1 2+(3889258819/5000000000 : ℝ)*X 2 0+(2492101261/10000000000 : ℝ)*X 2 1+(1531753871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-535705903/10000000000 : ℝ)*X 0 0+(1415878299/2500000000 : ℝ)*X 0 1+(2804614611/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((6188144527/10000000000 : ℝ)*X 1 0+(-7820371/156250000 : ℝ)*X 1 1+(127256079/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((3670548423/10000000000 : ℝ)*X 2 0+(3739505427/5000000000 : ℝ)*X 2 1+(-454334491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1696719659/2000000000 : ℝ)*X 0 0+(1510584327/10000000000 : ℝ)*X 0 1+(1502867963/10000000000 : ℝ)*X 0 2+(1696719659/2000000000 : ℝ)*X 1 0+(1510584327/10000000000 : ℝ)*X 1 1+(1502867963/10000000000 : ℝ)*X 1 2+(1696719659/2000000000 : ℝ)*X 2 0+(1510584327/10000000000 : ℝ)*X 2 1+(1502867963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318061_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((48493/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48493/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (272641346980269776695775949/12820721300000000000000000000000 : ℝ) := by norm_num
    linear_combination (55526287373/200000000000 : ℝ)*(base7) + (18936470511/31250000000 : ℝ)*(base59) + (4155141887757/1000000000000 : ℝ)*(major_s1_0) + (4155141887757/1000000000000 : ℝ)*(major_s1_1) + (4155141887757/1000000000000 : ℝ)*(major_s1_2) + (14421831/250000000000 : ℝ)*(sp_s1_0) + (13688733/500000000000 : ℝ)*(sp_s1_1) + (4415621/200000000000 : ℝ)*(sp_s1_6) + (587447138211/100000000000 : ℝ)*(sp_s1_7) + (5874550603977/1000000000000 : ℝ)*(sp_s1_8) + (5874605484519/1000000000000 : ℝ)*(sp_s1_9) + (102188454641/40000000000 : ℝ)*(sp_s1_13) + (19103771/250000000000 : ℝ)*(sp_s1_14) + (6875769/250000000000 : ℝ)*(sp_s1_15) + (455420401453/200000000000 : ℝ)*(f.failure) + (5874605484519/1000000000000 : ℝ)*(f.sum) + (4669980461830371559/25641442600000000000000000000000 : ℝ)*base63 + (484125758877463/595150000000000000000000000 : ℝ)*base65 + (253297788191813/538550000000000000000000000 : ℝ)*base67 + (57122428452817/476120000000000000000000000 : ℝ)*base69 + (420994067034746247/650856040000000000000000000000 : ℝ)*base71 + (67507257014233/273400000000000000000000000 : ℝ)*base72 + (36342296060497/538550000000000000000000000 : ℝ)*base75 + (52061912521863/273400000000000000000000000 : ℝ)*base76 + (323568519521802281/2944791400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (153/800000000000000 : ℝ)*base86 + (153/800000000000000 : ℝ)*base88 + (153/800000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13299/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13299/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1064118928519587023286872715357/122681482119700000000000000000000000 : ℝ) := by norm_num
    linear_combination (272696128089/500000000000 : ℝ)*(base7) + (6626241/1000000000000 : ℝ)*(base53) + (2713229861/40000000000 : ℝ)*(base59) + (1321651385637/500000000000 : ℝ)*(major_s1_0) + (1321651385637/500000000000 : ℝ)*(major_s1_1) + (2643296145033/1000000000000 : ℝ)*(major_s1_2) + (176143/62500000000 : ℝ)*(sp_s1_6) + (2107691/100000000000 : ℝ)*(sp_s1_7) + (2438209/125000000000 : ℝ)*(sp_s1_8) + (881622661187/250000000000 : ℝ)*(sp_s1_14) + (3526492215987/1000000000000 : ℝ)*(sp_s1_15) + (3526518347899/1000000000000 : ℝ)*(sp_s1_16) + (498481535633/250000000000 : ℝ)*(sp_s1_20) + (23405803/500000000000 : ℝ)*(sp_s1_27) + (181072939531/125000000000 : ℝ)*(f.failure) + (3526518347899/1000000000000 : ℝ)*(f.sum) + (80658960068363688741/179490098200000000000000000000000 : ℝ)*base63 + (141562436398241/297575000000000000000000000 : ℝ)*base65 + (193312129030381/1884925000000000000000000000 : ℝ)*base67 + (174115004477557/476120000000000000000000000 : ℝ)*base69 + (3571008384212499393/11389980700000000000000000000000 : ℝ)*base71 + (564263485326491/956900000000000000000000000 : ℝ)*base72 + (2223297570323773/3769850000000000000000000000 : ℝ)*base75 + (255829760739479/956900000000000000000000000 : ℝ)*base77 + (1563876358033785077/10306769900000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (231/500000000000000 : ℝ)*base86 + (231/500000000000000 : ℝ)*base88 + (231/500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48023/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48023/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (755483613843699572852253901389/61340741059850000000000000000000000 : ℝ) := by norm_num
    linear_combination (28036135713/100000000000 : ℝ)*(base7) + (7174227/1000000000000 : ℝ)*(base11) + (41270803041/200000000000 : ℝ)*(base40) + (184826848653/1000000000000 : ℝ)*(base59) + (1381909430001/500000000000 : ℝ)*(major_s1_0) + (1381909430001/500000000000 : ℝ)*(major_s1_1) + (1381909430001/500000000000 : ℝ)*(major_s1_2) + (2619581/500000000000 : ℝ)*(sp_s1_1) + (1058587/100000000000 : ℝ)*(sp_s1_2) + (33826813/250000000000 : ℝ)*(sp_s1_9) + (963217318677/250000000000 : ℝ)*(sp_s1_21) + (3852871209773/1000000000000 : ℝ)*(sp_s1_22) + (3852730555813/1000000000000 : ℝ)*(sp_s1_23) + (448747533419/250000000000 : ℝ)*(sp_s1_27) + (757314388273/500000000000 : ℝ)*(f.failure) + (770575289787/200000000000 : ℝ)*(f.sum) + (2009386310460623471/89745049100000000000000000000000 : ℝ)*base62 + (43942100391969/74393750000000000000000000 : ℝ)*base64 + (1390158739237257/1884925000000000000000000000 : ℝ)*base66 + (114559847025069/238060000000000000000000000 : ℝ)*base68 + (332146806341094559/455599228000000000000000000000 : ℝ)*base70 + (75301709898463/956900000000000000000000000 : ℝ)*base72 + (1893529957309831/3769850000000000000000000000 : ℝ)*base74 + (945869036885973/956900000000000000000000000 : ℝ)*base76 + (4049171705671713861/10306769900000000000000000000000 : ℝ)*base79 + (627/2000000000000000 : ℝ)*base87 + (627/2000000000000000 : ℝ)*base89 + (627/2000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((9569/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9569/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75397/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75397/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35709/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(35709/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((48493/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48493/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13299/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13299/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48023/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48023/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c318061_s1 p hpa hpb X hX hprev0

#print axioms solution

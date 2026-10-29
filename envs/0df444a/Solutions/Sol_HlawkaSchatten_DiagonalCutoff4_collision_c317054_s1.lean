-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c317054_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:14:55.214563+00:00
-- url     : https://prove2.me/submissions/c4a4c591-c6d8-4271-91e9-dd6b62da5e28

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
theorem collision_support_c317054_s1_s1_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5291940957/10000000000 : ℝ)*x 0 + (654491549/1250000000 : ℝ)*x 1 + (1703393739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291940957/10000000000 : ℝ)^39 ≤ (44904495988141/100000000000000 : ℝ)^31 := by
    have hnat : (5291940957 : ℕ)^39*100000000000000^31 ≤ 44904495988141^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291940957 10000000000 44904495988141 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654491549/1250000000 : ℝ)^39 ≤ (886148192953/2000000000000 : ℝ)^31 := by
    have hnat : (654491549 : ℕ)^39*2000000000000^31 ≤ 886148192953^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654491549 1250000000 886148192953 2000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1703393739/10000000000 : ℝ)^39 ≤ (5394047175479/50000000000000 : ℝ)^31 := by
    have hnat : (1703393739 : ℕ)^39*50000000000000^31 ≤ 5394047175479^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1703393739 10000000000 5394047175479 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291940957/10000000000 : ℝ), (654491549/1250000000 : ℝ), (1703393739/10000000000 : ℝ)] ![(44904495988141/100000000000000 : ℝ), (886148192953/2000000000000 : ℝ), (5394047175479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291940957/10000000000 : ℝ)|^39 ≤ (44904495988141/100000000000000 : ℝ)^31
        have hw : |(5291940957/10000000000 : ℝ)|=(5291940957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654491549/1250000000 : ℝ)|^39 ≤ (886148192953/2000000000000 : ℝ)^31
        have hw : |(654491549/1250000000 : ℝ)|=(654491549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1703393739/10000000000 : ℝ)|^39 ≤ (5394047175479/50000000000000 : ℝ)^31
        have hw : |(1703393739/10000000000 : ℝ)|=(1703393739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s1_s1_6 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5305618693/10000000000 : ℝ)*x 0 + (5261082791/10000000000 : ℝ)*x 1 + (-825614481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305618693/10000000000 : ℝ)^39 ≤ (45050557801289/100000000000000 : ℝ)^31 := by
    have hnat : (5305618693 : ℕ)^39*100000000000000^31 ≤ 45050557801289^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305618693 10000000000 45050557801289 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261082791/10000000000 : ℝ)^39 ≤ (2785957862397/6250000000000 : ℝ)^31 := by
    have hnat : (5261082791 : ℕ)^39*6250000000000^31 ≤ 2785957862397^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261082791 10000000000 2785957862397 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (825614481/5000000000 : ℝ)^39 ≤ (5187058194087/50000000000000 : ℝ)^31 := by
    have hnat : (825614481 : ℕ)^39*50000000000000^31 ≤ 5187058194087^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825614481 5000000000 5187058194087 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305618693/10000000000 : ℝ), (5261082791/10000000000 : ℝ), (-825614481/5000000000 : ℝ)] ![(45050557801289/100000000000000 : ℝ), (2785957862397/6250000000000 : ℝ), (5187058194087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305618693/10000000000 : ℝ)|^39 ≤ (45050557801289/100000000000000 : ℝ)^31
        have hw : |(5305618693/10000000000 : ℝ)|=(5305618693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261082791/10000000000 : ℝ)|^39 ≤ (2785957862397/6250000000000 : ℝ)^31
        have hw : |(5261082791/10000000000 : ℝ)|=(5261082791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-825614481/5000000000 : ℝ)|^39 ≤ (5187058194087/50000000000000 : ℝ)^31
        have hw : |(-825614481/5000000000 : ℝ)|=(825614481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s1_s1_7 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-21806513/500000000 : ℝ)*x 0 + (407672527/1000000000 : ℝ)*x 1 + (-1790658543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21806513/500000000 : ℝ)^39 ≤ (242917862789/12500000000000 : ℝ)^31 := by
    have hnat : (21806513 : ℕ)^39*12500000000000^31 ≤ 242917862789^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21806513 500000000 242917862789 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (407672527/1000000000 : ℝ)^39 ≤ (4042561821171/12500000000000 : ℝ)^31 := by
    have hnat : (407672527 : ℕ)^39*12500000000000^31 ≤ 4042561821171^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407672527 1000000000 4042561821171 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1790658543/2500000000 : ℝ)^39 ≤ (8214520314563/12500000000000 : ℝ)^31 := by
    have hnat : (1790658543 : ℕ)^39*12500000000000^31 ≤ 8214520314563^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1790658543 2500000000 8214520314563 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21806513/500000000 : ℝ), (407672527/1000000000 : ℝ), (-1790658543/2500000000 : ℝ)] ![(242917862789/12500000000000 : ℝ), (4042561821171/12500000000000 : ℝ), (8214520314563/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21806513/500000000 : ℝ)|^39 ≤ (242917862789/12500000000000 : ℝ)^31
        have hw : |(-21806513/500000000 : ℝ)|=(21806513/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(407672527/1000000000 : ℝ)|^39 ≤ (4042561821171/12500000000000 : ℝ)^31
        have hw : |(407672527/1000000000 : ℝ)|=(407672527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1790658543/2500000000 : ℝ)|^39 ≤ (8214520314563/12500000000000 : ℝ)^31
        have hw : |(-1790658543/2500000000 : ℝ)|=(1790658543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s1_s1_8 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1297659989/2500000000 : ℝ)*x 0 + (-755719487/10000000000 : ℝ)*x 1 + (-5973137673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1297659989/2500000000 : ℝ)^39 ≤ (43825767078843/100000000000000 : ℝ)^31 := by
    have hnat : (1297659989 : ℕ)^39*100000000000000^31 ≤ 43825767078843^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297659989 2500000000 43825767078843 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (755719487/10000000000 : ℝ)^39 ≤ (1940328674651/50000000000000 : ℝ)^31 := by
    have hnat : (755719487 : ℕ)^39*50000000000000^31 ≤ 1940328674651^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755719487 10000000000 1940328674651 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5973137673/10000000000 : ℝ)^39 ≤ (10458715112193/20000000000000 : ℝ)^31 := by
    have hnat : (5973137673 : ℕ)^39*20000000000000^31 ≤ 10458715112193^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5973137673 10000000000 10458715112193 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1297659989/2500000000 : ℝ), (-755719487/10000000000 : ℝ), (-5973137673/10000000000 : ℝ)] ![(43825767078843/100000000000000 : ℝ), (1940328674651/50000000000000 : ℝ), (10458715112193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1297659989/2500000000 : ℝ)|^39 ≤ (43825767078843/100000000000000 : ℝ)^31
        have hw : |(1297659989/2500000000 : ℝ)|=(1297659989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-755719487/10000000000 : ℝ)|^39 ≤ (1940328674651/50000000000000 : ℝ)^31
        have hw : |(-755719487/10000000000 : ℝ)|=(755719487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5973137673/10000000000 : ℝ)|^39 ≤ (10458715112193/20000000000000 : ℝ)^31
        have hw : |(-5973137673/10000000000 : ℝ)|=(5973137673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s1_s1_9 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (147053211/312500000 : ℝ)*x 0 + (327272873/500000000 : ℝ)*x 1 + (547724037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (147053211/312500000 : ℝ)^39 ≤ (9684573433383/25000000000000 : ℝ)^31 := by
    have hnat : (147053211 : ℕ)^39*25000000000000^31 ≤ 9684573433383^31*312500000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147053211 312500000 9684573433383 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327272873/500000000 : ℝ)^39 ≤ (93877309357/160000000000 : ℝ)^31 := by
    have hnat : (327272873 : ℕ)^39*160000000000^31 ≤ 93877309357^31*500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327272873 500000000 93877309357 160000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547724037/10000000000 : ℝ)^39 ≤ (32354848819/1250000000000 : ℝ)^31 := by
    have hnat : (547724037 : ℕ)^39*1250000000000^31 ≤ 32354848819^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547724037 10000000000 32354848819 1250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(147053211/312500000 : ℝ), (327272873/500000000 : ℝ), (547724037/10000000000 : ℝ)] ![(9684573433383/25000000000000 : ℝ), (93877309357/160000000000 : ℝ), (32354848819/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(147053211/312500000 : ℝ)|^39 ≤ (9684573433383/25000000000000 : ℝ)^31
        have hw : |(147053211/312500000 : ℝ)|=(147053211/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327272873/500000000 : ℝ)|^39 ≤ (93877309357/160000000000 : ℝ)^31
        have hw : |(327272873/500000000 : ℝ)|=(327272873/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547724037/10000000000 : ℝ)|^39 ≤ (32354848819/1250000000000 : ℝ)^31
        have hw : |(547724037/10000000000 : ℝ)|=(547724037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s1_s1_13 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2451741933/5000000000 : ℝ)*x 0 + (50166069/78125000 : ℝ)*x 1 + (-433076877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2451741933/5000000000 : ℝ)^39 ≤ (40797636947289/100000000000000 : ℝ)^31 := by
    have hnat : (2451741933 : ℕ)^39*100000000000000^31 ≤ 40797636947289^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2451741933 5000000000 40797636947289 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50166069/78125000 : ℝ)^39 ≤ (1145522424831/2000000000000 : ℝ)^31 := by
    have hnat : (50166069 : ℕ)^39*2000000000000^31 ≤ 1145522424831^31*78125000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50166069 78125000 1145522424831 2000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433076877/10000000000 : ℝ)^39 ≤ (30097528049/1562500000000 : ℝ)^31 := by
    have hnat : (433076877 : ℕ)^39*1562500000000^31 ≤ 30097528049^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433076877 10000000000 30097528049 1562500000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2451741933/5000000000 : ℝ), (50166069/78125000 : ℝ), (-433076877/10000000000 : ℝ)] ![(40797636947289/100000000000000 : ℝ), (1145522424831/2000000000000 : ℝ), (30097528049/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2451741933/5000000000 : ℝ)|^39 ≤ (40797636947289/100000000000000 : ℝ)^31
        have hw : |(2451741933/5000000000 : ℝ)|=(2451741933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(50166069/78125000 : ℝ)|^39 ≤ (1145522424831/2000000000000 : ℝ)^31
        have hw : |(50166069/78125000 : ℝ)|=(50166069/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-433076877/10000000000 : ℝ)|^39 ≤ (30097528049/1562500000000 : ℝ)^31
        have hw : |(-433076877/10000000000 : ℝ)|=(433076877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s1_s1_14 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-12055041/5000000000 : ℝ)*x 0 + (2140529553/5000000000 : ℝ)*x 1 + (-3574390391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12055041/5000000000 : ℝ)^39 ≤ (25445269953/50000000000000 : ℝ)^31 := by
    have hnat : (12055041 : ℕ)^39*50000000000000^31 ≤ 25445269953^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12055041 5000000000 25445269953 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2140529553/5000000000 : ℝ)^39 ≤ (17196405329133/50000000000000 : ℝ)^31 := by
    have hnat : (2140529553 : ℕ)^39*50000000000000^31 ≤ 17196405329133^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140529553 5000000000 17196405329133 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3574390391/5000000000 : ℝ)^39 ≤ (32778149391973/50000000000000 : ℝ)^31 := by
    have hnat : (3574390391 : ℕ)^39*50000000000000^31 ≤ 32778149391973^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3574390391 5000000000 32778149391973 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12055041/5000000000 : ℝ), (2140529553/5000000000 : ℝ), (-3574390391/5000000000 : ℝ)] ![(25445269953/50000000000000 : ℝ), (17196405329133/50000000000000 : ℝ), (32778149391973/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12055041/5000000000 : ℝ)|^39 ≤ (25445269953/50000000000000 : ℝ)^31
        have hw : |(-12055041/5000000000 : ℝ)|=(12055041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2140529553/5000000000 : ℝ)|^39 ≤ (17196405329133/50000000000000 : ℝ)^31
        have hw : |(2140529553/5000000000 : ℝ)|=(2140529553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3574390391/5000000000 : ℝ)|^39 ≤ (32778149391973/50000000000000 : ℝ)^31
        have hw : |(-3574390391/5000000000 : ℝ)|=(3574390391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s1_s1_15 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2317247119/5000000000 : ℝ)*x 0 + (-140726207/1000000000 : ℝ)*x 1 + (-6083657069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2317247119/5000000000 : ℝ)^39 ≤ (9500564535657/25000000000000 : ℝ)^31 := by
    have hnat : (2317247119 : ℕ)^39*25000000000000^31 ≤ 9500564535657^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317247119 5000000000 9500564535657 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140726207/1000000000 : ℝ)^39 ≤ (8484002428131/100000000000000 : ℝ)^31 := by
    have hnat : (140726207 : ℕ)^39*100000000000000^31 ≤ 8484002428131^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140726207 1000000000 8484002428131 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6083657069/10000000000 : ℝ)^39 ≤ (13378434852679/25000000000000 : ℝ)^31 := by
    have hnat : (6083657069 : ℕ)^39*25000000000000^31 ≤ 13378434852679^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6083657069 10000000000 13378434852679 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2317247119/5000000000 : ℝ), (-140726207/1000000000 : ℝ), (-6083657069/10000000000 : ℝ)] ![(9500564535657/25000000000000 : ℝ), (8484002428131/100000000000000 : ℝ), (13378434852679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2317247119/5000000000 : ℝ)|^39 ≤ (9500564535657/25000000000000 : ℝ)^31
        have hw : |(2317247119/5000000000 : ℝ)|=(2317247119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-140726207/1000000000 : ℝ)|^39 ≤ (8484002428131/100000000000000 : ℝ)^31
        have hw : |(-140726207/1000000000 : ℝ)|=(140726207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6083657069/10000000000 : ℝ)|^39 ≤ (13378434852679/25000000000000 : ℝ)^31
        have hw : |(-6083657069/10000000000 : ℝ)|=(6083657069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s1_s1_16 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6740735613/10000000000 : ℝ)*x 0 + (2223986037/5000000000 : ℝ)*x 1 + (310219179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6740735613/10000000000 : ℝ)^39 ≤ (15220984114241/25000000000000 : ℝ)^31 := by
    have hnat : (6740735613 : ℕ)^39*25000000000000^31 ≤ 15220984114241^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6740735613 10000000000 15220984114241 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2223986037/5000000000 : ℝ)^39 ≤ (2255512194359/6250000000000 : ℝ)^31 := by
    have hnat : (2223986037 : ℕ)^39*6250000000000^31 ≤ 2255512194359^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223986037 5000000000 2255512194359 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310219179/5000000000 : ℝ)^39 ≤ (151393421023/5000000000000 : ℝ)^31 := by
    have hnat : (310219179 : ℕ)^39*5000000000000^31 ≤ 151393421023^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310219179 5000000000 151393421023 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6740735613/10000000000 : ℝ), (2223986037/5000000000 : ℝ), (310219179/5000000000 : ℝ)] ![(15220984114241/25000000000000 : ℝ), (2255512194359/6250000000000 : ℝ), (151393421023/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6740735613/10000000000 : ℝ)|^39 ≤ (15220984114241/25000000000000 : ℝ)^31
        have hw : |(6740735613/10000000000 : ℝ)|=(6740735613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2223986037/5000000000 : ℝ)|^39 ≤ (2255512194359/6250000000000 : ℝ)^31
        have hw : |(2223986037/5000000000 : ℝ)|=(2223986037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(310219179/5000000000 : ℝ)|^39 ≤ (151393421023/5000000000000 : ℝ)^31
        have hw : |(310219179/5000000000 : ℝ)|=(310219179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s1_s1_20 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1596450629/2500000000 : ℝ)*x 0 + (1463167/3125000 : ℝ)*x 1 + (-217285519/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1596450629/2500000000 : ℝ)^39 ≤ (56878549378331/100000000000000 : ℝ)^31 := by
    have hnat : (1596450629 : ℕ)^39*100000000000000^31 ≤ 56878549378331^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596450629 2500000000 56878549378331 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1463167/3125000 : ℝ)^39 ≤ (4811795339823/12500000000000 : ℝ)^31 := by
    have hnat : (1463167 : ℕ)^39*12500000000000^31 ≤ 4811795339823^31*3125000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1463167 3125000 4811795339823 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217285519/2500000000 : ℝ)^39 ≤ (2313543947083/50000000000000 : ℝ)^31 := by
    have hnat : (217285519 : ℕ)^39*50000000000000^31 ≤ 2313543947083^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217285519 2500000000 2313543947083 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1596450629/2500000000 : ℝ), (1463167/3125000 : ℝ), (-217285519/2500000000 : ℝ)] ![(56878549378331/100000000000000 : ℝ), (4811795339823/12500000000000 : ℝ), (2313543947083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1596450629/2500000000 : ℝ)|^39 ≤ (56878549378331/100000000000000 : ℝ)^31
        have hw : |(1596450629/2500000000 : ℝ)|=(1596450629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1463167/3125000 : ℝ)|^39 ≤ (4811795339823/12500000000000 : ℝ)^31
        have hw : |(1463167/3125000 : ℝ)|=(1463167/3125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-217285519/2500000000 : ℝ)|^39 ≤ (2313543947083/50000000000000 : ℝ)^31
        have hw : |(-217285519/2500000000 : ℝ)|=(217285519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s1_s1_21 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1507/312500000 : ℝ)*x 0 + (133881693/250000000 : ℝ)*x 1 + (-616526651/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1507/312500000 : ℝ)^39 ≤ (10236987/50000000000000 : ℝ)^31 := by
    have hnat : (1507 : ℕ)^39*50000000000000^31 ≤ 10236987^31*312500000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507 312500000 10236987 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133881693/250000000 : ℝ)^39 ≤ (22790782655403/50000000000000 : ℝ)^31 := by
    have hnat : (133881693 : ℕ)^39*50000000000000^31 ≤ 22790782655403^31*250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133881693 250000000 22790782655403 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (616526651/1000000000 : ℝ)^39 ≤ (54418414202869/100000000000000 : ℝ)^31 := by
    have hnat : (616526651 : ℕ)^39*100000000000000^31 ≤ 54418414202869^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      616526651 1000000000 54418414202869 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1507/312500000 : ℝ), (133881693/250000000 : ℝ), (-616526651/1000000000 : ℝ)] ![(10236987/50000000000000 : ℝ), (22790782655403/50000000000000 : ℝ), (54418414202869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1507/312500000 : ℝ)|^39 ≤ (10236987/50000000000000 : ℝ)^31
        have hw : |(-1507/312500000 : ℝ)|=(1507/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(133881693/250000000 : ℝ)|^39 ≤ (22790782655403/50000000000000 : ℝ)^31
        have hw : |(133881693/250000000 : ℝ)|=(133881693/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-616526651/1000000000 : ℝ)|^39 ≤ (54418414202869/100000000000000 : ℝ)^31
        have hw : |(-616526651/1000000000 : ℝ)|=(616526651/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s1_s1_22 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3260389513/5000000000 : ℝ)*x 0 + (-310101319/2500000000 : ℝ)*x 1 + (-2139223809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3260389513/5000000000 : ℝ)^39 ≤ (58395148772863/100000000000000 : ℝ)^31 := by
    have hnat : (3260389513 : ℕ)^39*100000000000000^31 ≤ 58395148772863^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3260389513 5000000000 58395148772863 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (310101319/2500000000 : ℝ)^39 ≤ (7238432603869/100000000000000 : ℝ)^31 := by
    have hnat : (310101319 : ℕ)^39*100000000000000^31 ≤ 7238432603869^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310101319 2500000000 7238432603869 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2139223809/5000000000 : ℝ)^39 ≤ (34366418603581/100000000000000 : ℝ)^31 := by
    have hnat : (2139223809 : ℕ)^39*100000000000000^31 ≤ 34366418603581^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139223809 5000000000 34366418603581 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3260389513/5000000000 : ℝ), (-310101319/2500000000 : ℝ), (-2139223809/5000000000 : ℝ)] ![(58395148772863/100000000000000 : ℝ), (7238432603869/100000000000000 : ℝ), (34366418603581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3260389513/5000000000 : ℝ)|^39 ≤ (58395148772863/100000000000000 : ℝ)^31
        have hw : |(3260389513/5000000000 : ℝ)|=(3260389513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-310101319/2500000000 : ℝ)|^39 ≤ (7238432603869/100000000000000 : ℝ)^31
        have hw : |(-310101319/2500000000 : ℝ)|=(310101319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2139223809/5000000000 : ℝ)|^39 ≤ (34366418603581/100000000000000 : ℝ)^31
        have hw : |(-2139223809/5000000000 : ℝ)|=(2139223809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s1_s1_23 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5054583551/10000000000 : ℝ)*x 0 + (5486116037/10000000000 : ℝ)*x 1 + (1683198659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5054583551/10000000000 : ℝ)^39 ≤ (42385478523087/100000000000000 : ℝ)^31 := by
    have hnat : (5054583551 : ℕ)^39*100000000000000^31 ≤ 42385478523087^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5054583551 10000000000 42385478523087 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5486116037/10000000000 : ℝ)^39 ≤ (23493544218557/50000000000000 : ℝ)^31 := by
    have hnat : (5486116037 : ℕ)^39*50000000000000^31 ≤ 23493544218557^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486116037 10000000000 23493544218557 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1683198659/10000000000 : ℝ)^39 ≤ (10627433029063/100000000000000 : ℝ)^31 := by
    have hnat : (1683198659 : ℕ)^39*100000000000000^31 ≤ 10627433029063^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683198659 10000000000 10627433029063 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5054583551/10000000000 : ℝ), (5486116037/10000000000 : ℝ), (1683198659/10000000000 : ℝ)] ![(42385478523087/100000000000000 : ℝ), (23493544218557/50000000000000 : ℝ), (10627433029063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5054583551/10000000000 : ℝ)|^39 ≤ (42385478523087/100000000000000 : ℝ)^31
        have hw : |(5054583551/10000000000 : ℝ)|=(5054583551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5486116037/10000000000 : ℝ)|^39 ≤ (23493544218557/50000000000000 : ℝ)^31
        have hw : |(5486116037/10000000000 : ℝ)|=(5486116037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1683198659/10000000000 : ℝ)|^39 ≤ (10627433029063/100000000000000 : ℝ)^31
        have hw : |(1683198659/10000000000 : ℝ)|=(1683198659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317054_s1_s1_27 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2973448177/5000000000 : ℝ)*x 0 + (2357628643/5000000000 : ℝ)*x 1 + (-747713247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2973448177/5000000000 : ℝ)^39 ≤ (52004715258629/100000000000000 : ℝ)^31 := by
    have hnat : (2973448177 : ℕ)^39*100000000000000^31 ≤ 52004715258629^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2973448177 5000000000 52004715258629 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2357628643/5000000000 : ℝ)^39 ≤ (485465906513/1250000000000 : ℝ)^31 := by
    have hnat : (2357628643 : ℕ)^39*1250000000000^31 ≤ 485465906513^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2357628643 5000000000 485465906513 1250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (747713247/5000000000 : ℝ)^39 ≤ (2289503050811/25000000000000 : ℝ)^31 := by
    have hnat : (747713247 : ℕ)^39*25000000000000^31 ≤ 2289503050811^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747713247 5000000000 2289503050811 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2973448177/5000000000 : ℝ), (2357628643/5000000000 : ℝ), (-747713247/5000000000 : ℝ)] ![(52004715258629/100000000000000 : ℝ), (485465906513/1250000000000 : ℝ), (2289503050811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2973448177/5000000000 : ℝ)|^39 ≤ (52004715258629/100000000000000 : ℝ)^31
        have hw : |(2973448177/5000000000 : ℝ)|=(2973448177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2357628643/5000000000 : ℝ)|^39 ≤ (485465906513/1250000000000 : ℝ)^31
        have hw : |(2357628643/5000000000 : ℝ)|=(2357628643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-747713247/5000000000 : ℝ)|^39 ≤ (2289503050811/25000000000000 : ℝ)^31
        have hw : |(-747713247/5000000000 : ℝ)|=(747713247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317054_s1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((73497/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73497/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(77167/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(77167/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13601/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-13601/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1513/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1513/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(51443/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(51443/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38993/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38993/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (34473/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (73497/100000 : ℝ) ^ (77/16 : ℝ) ≤ (4544148395445264019/20000000000000000000 : ℝ) := by
    have hpowers : (73497/100000 : ℝ)^77 ≤ (4544148395445264019/20000000000000000000 : ℝ)^16 := by
      have hnat : (73497 : ℕ)^77*20000000000000000000^16 ≤ 4544148395445264019^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73497 100000 4544148395445264019 20000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73497/100000 : ℝ)) (X := (4544148395445264019/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (24544148395445264019/20000000000000000000 : ℝ) ≤ (10434615769121353/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (24544148395445264019/20000000000000000000 : ℝ)^16 ≤ (10434615769121353/10000000000000000 : ℝ)^77 := by
      have hnat : (24544148395445264019 : ℕ)^16*10000000000000000^77 ≤ 10434615769121353^77*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24544148395445264019 20000000000000000000 10434615769121353 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10434615769121353/10000000000000000 : ℝ)) (X := (24544148395445264019/20000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (14544148395445264019/10000000000000000000 : ℝ) ≤ (2161898778230003/2000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (14544148395445264019/10000000000000000000 : ℝ)^16 ≤ (2161898778230003/2000000000000000 : ℝ)^77 := by
      have hnat : (14544148395445264019 : ℕ)^16*2000000000000000^77 ≤ 2161898778230003^77*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14544148395445264019 10000000000000000000 2161898778230003 2000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2161898778230003/2000000000000000 : ℝ)) (X := (14544148395445264019/10000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(144871923040451/2449900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(62479687004777/1224950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (73497/100000 : ℝ)) (alpha := (144871923040451/2449900000000000 : ℝ)) (beta := (62479687004777/1224950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (73497/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(144871923040451/2449900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(62479687004777/1224950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (77167/100000 : ℝ) ^ (77/16 : ℝ) ≤ (14362652711638558541/50000000000000000000 : ℝ) := by
    have hpowers : (77167/100000 : ℝ)^77 ≤ (14362652711638558541/50000000000000000000 : ℝ)^16 := by
      have hnat : (77167 : ℕ)^77*50000000000000000000^16 ≤ 14362652711638558541^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77167 100000 14362652711638558541 50000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (77167/100000 : ℝ)) (X := (14362652711638558541/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (64362652711638558541/50000000000000000000 : ℝ) ≤ (5269353257568357/5000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (64362652711638558541/50000000000000000000 : ℝ)^16 ≤ (5269353257568357/5000000000000000 : ℝ)^77 := by
      have hnat : (64362652711638558541 : ℕ)^16*5000000000000000^77 ≤ 5269353257568357^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64362652711638558541 50000000000000000000 5269353257568357 5000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5269353257568357/5000000000000000 : ℝ)) (X := (64362652711638558541/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (39362652711638558541/25000000000000000000 : ℝ) ≤ (10989174246895057/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (39362652711638558541/25000000000000000000 : ℝ)^16 ≤ (10989174246895057/10000000000000000 : ℝ)^77 := by
      have hnat : (39362652711638558541 : ℕ)^16*10000000000000000^77 ≤ 10989174246895057^77*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39362652711638558541 25000000000000000000 10989174246895057 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10989174246895057/10000000000000000 : ℝ)) (X := (39362652711638558541/25000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(269353257568357/3858350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(450467731758343/7716700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (77167/100000 : ℝ)) (alpha := (269353257568357/3858350000000000 : ℝ)) (beta := (450467731758343/7716700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (77167/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(269353257568357/3858350000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(450467731758343/7716700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13601/20000 : ℝ) ^ (77/16 : ℝ) ≤ (15635177512289061279/100000000000000000000 : ℝ) := by
    have hpowers : (13601/20000 : ℝ)^77 ≤ (15635177512289061279/100000000000000000000 : ℝ)^16 := by
      have hnat : (13601 : ℕ)^77*100000000000000000000^16 ≤ 15635177512289061279^16*20000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13601 20000 15635177512289061279 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13601/20000 : ℝ)) (X := (15635177512289061279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (115635177512289061279/100000000000000000000 : ℝ) ≤ (10306461954846731/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (115635177512289061279/100000000000000000000 : ℝ)^16 ≤ (10306461954846731/10000000000000000 : ℝ)^77 := by
      have hnat : (115635177512289061279 : ℕ)^16*10000000000000000^77 ≤ 10306461954846731^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        115635177512289061279 100000000000000000000 10306461954846731 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10306461954846731/10000000000000000 : ℝ)) (X := (115635177512289061279/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (65635177512289061279/50000000000000000000 : ℝ) ≤ (10581667505755759/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (65635177512289061279/50000000000000000000 : ℝ)^16 ≤ (10581667505755759/10000000000000000 : ℝ)^77 := by
      have hnat : (65635177512289061279 : ℕ)^16*10000000000000000^77 ≤ 10581667505755759^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65635177512289061279 50000000000000000000 10581667505755759 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10581667505755759/10000000000000000 : ℝ)) (X := (65635177512289061279/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(306461954846731/6800500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(68801387727257/1700125000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (13601/20000 : ℝ)) (alpha := (306461954846731/6800500000000000 : ℝ)) (beta := (68801387727257/1700125000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (13601/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(306461954846731/6800500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(68801387727257/1700125000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_2 : ((5291940957/10000000000 : ℝ)*X 2 0+(654491549/1250000000 : ℝ)*X 2 1+(1703393739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5305618693/10000000000 : ℝ)*X 0 0+(5261082791/10000000000 : ℝ)*X 0 1+(-825614481/5000000000 : ℝ)*X 0 2+(5305618693/10000000000 : ℝ)*X 1 0+(5261082791/10000000000 : ℝ)*X 1 1+(-825614481/5000000000 : ℝ)*X 1 2+(5305618693/10000000000 : ℝ)*X 2 0+(5261082791/10000000000 : ℝ)*X 2 1+(-825614481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-21806513/500000000 : ℝ)*X 0 0+(407672527/1000000000 : ℝ)*X 0 1+(-1790658543/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1297659989/2500000000 : ℝ)*X 1 0+(-755719487/10000000000 : ℝ)*X 1 1+(-5973137673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((147053211/312500000 : ℝ)*X 2 0+(327272873/500000000 : ℝ)*X 2 1+(547724037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((2451741933/5000000000 : ℝ)*X 0 0+(50166069/78125000 : ℝ)*X 0 1+(-433076877/10000000000 : ℝ)*X 0 2+(2451741933/5000000000 : ℝ)*X 1 0+(50166069/78125000 : ℝ)*X 1 1+(-433076877/10000000000 : ℝ)*X 1 2+(2451741933/5000000000 : ℝ)*X 2 0+(50166069/78125000 : ℝ)*X 2 1+(-433076877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-12055041/5000000000 : ℝ)*X 0 0+(2140529553/5000000000 : ℝ)*X 0 1+(-3574390391/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2317247119/5000000000 : ℝ)*X 1 0+(-140726207/1000000000 : ℝ)*X 1 1+(-6083657069/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6740735613/10000000000 : ℝ)*X 2 0+(2223986037/5000000000 : ℝ)*X 2 1+(310219179/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1596450629/2500000000 : ℝ)*X 0 0+(1463167/3125000 : ℝ)*X 0 1+(-217285519/2500000000 : ℝ)*X 0 2+(1596450629/2500000000 : ℝ)*X 1 0+(1463167/3125000 : ℝ)*X 1 1+(-217285519/2500000000 : ℝ)*X 1 2+(1596450629/2500000000 : ℝ)*X 2 0+(1463167/3125000 : ℝ)*X 2 1+(-217285519/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-1507/312500000 : ℝ)*X 0 0+(133881693/250000000 : ℝ)*X 0 1+(-616526651/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3260389513/5000000000 : ℝ)*X 1 0+(-310101319/2500000000 : ℝ)*X 1 1+(-2139223809/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((5054583551/10000000000 : ℝ)*X 2 0+(5486116037/10000000000 : ℝ)*X 2 1+(1683198659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((2973448177/5000000000 : ℝ)*X 0 0+(2357628643/5000000000 : ℝ)*X 0 1+(-747713247/5000000000 : ℝ)*X 0 2+(2973448177/5000000000 : ℝ)*X 1 0+(2357628643/5000000000 : ℝ)*X 1 1+(-747713247/5000000000 : ℝ)*X 1 2+(2973448177/5000000000 : ℝ)*X 2 0+(2357628643/5000000000 : ℝ)*X 2 1+(-747713247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317054_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((1513/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1513/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13232592890936927048017517340621/918317337254750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1198887/62500000000 : ℝ)*(base23) + (256667813007/1000000000000 : ℝ)*(base39) + (389928184701/1000000000000 : ℝ)*(base60) + (4114352966029/1000000000000 : ℝ)*(major_s1_0) + (4114352966029/1000000000000 : ℝ)*(major_s1_1) + (4114352966029/1000000000000 : ℝ)*(major_s1_2) + (5827441/200000000000 : ℝ)*(sp_s1_6) + (7426414037/1250000000 : ℝ)*(sp_s1_7) + (1485282569581/250000000000 : ℝ)*(sp_s1_8) + (742643211247/125000000000 : ℝ)*(sp_s1_9) + (228747626473/100000000000 : ℝ)*(sp_s1_13) + (32248657/500000000000 : ℝ)*(sp_s1_14) + (6544859/100000000000 : ℝ)*(sp_s1_15) + (15427373/500000000000 : ℝ)*(sp_s1_23) + (457501080387/200000000000 : ℝ)*(f.failure) + (2970597863457/500000000000 : ℝ)*(f.sum) + (323364618811510904813/524774183500000000000000000000000 : ℝ)*base63 + (1483812692650069/3400250000000000000000000000 : ℝ)*base64 + (2446205773610613/7716700000000000000000000000 : ℝ)*base67 + (2176580658710749/6800500000000000000000000000 : ℝ)*base69 + (21774409988914492067/166605449500000000000000000000000 : ℝ)*base70 + (845058505704623/1224950000000000000000000000 : ℝ)*base73 + (22776617079597/241146875000000000000000000 : ℝ)*base74 + (130060777455151/2449900000000000000000000000 : ℝ)*base76 + (58421091580348039489/189051433300000000000000000000000 : ℝ)*base79 + (6703/10000000000000000 : ℝ)*base86 + (6703/10000000000000000 : ℝ)*base88 + (6703/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(51443/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(51443/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (47305416965270592812160849/11900389250000000000000000000000 : ℝ) := by norm_num
    linear_combination (9960218489/40000000000 : ℝ)*(base7) + (145797962913/1000000000000 : ℝ)*(base39) + (1082577239/62500000000 : ℝ)*(base60) + (906242490197/250000000000 : ℝ)*(major_s1_0) + (906242490197/250000000000 : ℝ)*(major_s1_1) + (906242490197/250000000000 : ℝ)*(major_s1_2) + (1469/15625000000 : ℝ)*(sp_s1_2) + (28491147/1000000000000 : ℝ)*(sp_s1_8) + (5091452248453/1000000000000 : ℝ)*(sp_s1_14) + (127285666583/25000000000 : ℝ)*(sp_s1_15) + (5091455060451/1000000000000 : ℝ)*(sp_s1_16) + (1132209815133/500000000000 : ℝ)*(sp_s1_20) + (581203/200000000000 : ℝ)*(sp_s1_21) + (3185701/1000000000000 : ℝ)*(sp_s1_27) + (1007708676871/500000000000 : ℝ)*(f.failure) + (5091455154467/1000000000000 : ℝ)*(f.sum) + (23054112686118767641/131193545875000000000000000000000 : ℝ)*base62 + (112373395977429/425031250000000000000000000 : ℝ)*base65 + (460018045897967/964587500000000000000000000 : ℝ)*base67 + (13138375461423/106257812500000000000000000 : ℝ)*base68 + (56278051499167132363/83302724750000000000000000000000 : ℝ)*base71 + (745258961115829/1224950000000000000000000000 : ℝ)*base72 + (1395941004975841/3858350000000000000000000000 : ℝ)*base75 + (182932794697677/612475000000000000000000000 : ℝ)*base77 + (21539044169985000573/47262858325000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (14099/25000000000000000 : ℝ)*base86 + (14099/25000000000000000 : ℝ)*base88 + (14099/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38993/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38993/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (91179942090649775273826464628237/6428221360783250000000000000000000000 : ℝ) := by norm_num
    linear_combination (16303004491/125000000000 : ℝ)*(base7) + (4573/125000000000 : ℝ)*(base15) + (136617265233/200000000000 : ℝ)*(base39) + (4275402363223/1000000000000 : ℝ)*(major_s1_0) + (4275402363223/1000000000000 : ℝ)*(major_s1_1) + (4275402363223/1000000000000 : ℝ)*(major_s1_2) + (1182129/4000000000 : ℝ)*(sp_s1_2) + (37989419/500000000000 : ℝ)*(sp_s1_6) + (17445167/250000000000 : ℝ)*(sp_s1_9) + (58653113/500000000000 : ℝ)*(sp_s1_20) + (3049409465741/500000000000 : ℝ)*(sp_s1_21) + (6098818894899/1000000000000 : ℝ)*(sp_s1_22) + (1219690723713/200000000000 : ℝ)*(sp_s1_23) + (4897024781/1953125000 : ℝ)*(sp_s1_27) + (2377045937009/1000000000000 : ℝ)*(f.failure) + (3049409465741/500000000000 : ℝ)*(f.sum) + (247826850094539318781/524774183500000000000000000000000 : ℝ)*base63 + (625642751161593/850062500000000000000000000 : ℝ)*base65 + (3812806592953089/7716700000000000000000000000 : ℝ)*base66 + (1232021231493413/6800500000000000000000000000 : ℝ)*base69 + (78265193592381538921/166605449500000000000000000000000 : ℝ)*base71 + (306389372397861/1224950000000000000000000000 : ℝ)*base73 + (570961666195273/1929175000000000000000000000 : ℝ)*base75 + (344992049546923/2449900000000000000000000000 : ℝ)*base77 + (15448050538672403173/189051433300000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (6379/50000000000000000 : ℝ)*base87 + (6379/50000000000000000 : ℝ)*base89 + (6379/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((73497/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73497/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(77167/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(77167/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13601/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-13601/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1513/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1513/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(51443/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(51443/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38993/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38993/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c317054_s1 p hpa hpb X hX hprev0

#print axioms solution

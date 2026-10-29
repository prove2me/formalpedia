-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c316054_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:07:13.909131+00:00
-- url     : https://prove2.me/submissions/af1808a7-6bfb-45b8-b0ad-19ef52ab8b43

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
theorem collision_support_c316054_s2_s2_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-166432869/1250000000 : ℝ)*x 0 + (4526332813/10000000000 : ℝ)*x 1 + (-3131123053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166432869/1250000000 : ℝ)^77 ≤ (7845938736477/100000000000000 : ℝ)^61 := by
    have hnat : (166432869 : ℕ)^77*100000000000000^61 ≤ 7845938736477^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166432869 1250000000 7845938736477 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4526332813/10000000000 : ℝ)^77 ≤ (367663468009/1000000000000 : ℝ)^61 := by
    have hnat : (4526332813 : ℕ)^77*1000000000000^61 ≤ 367663468009^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526332813 10000000000 367663468009 1000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3131123053/5000000000 : ℝ)^77 ≤ (6923464305833/12500000000000 : ℝ)^61 := by
    have hnat : (3131123053 : ℕ)^77*12500000000000^61 ≤ 6923464305833^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3131123053 5000000000 6923464305833 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-166432869/1250000000 : ℝ), (4526332813/10000000000 : ℝ), (-3131123053/5000000000 : ℝ)] ![(7845938736477/100000000000000 : ℝ), (367663468009/1000000000000 : ℝ), (6923464305833/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-166432869/1250000000 : ℝ)|^77 ≤ (7845938736477/100000000000000 : ℝ)^61
        have hw : |(-166432869/1250000000 : ℝ)|=(166432869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4526332813/10000000000 : ℝ)|^77 ≤ (367663468009/1000000000000 : ℝ)^61
        have hw : |(4526332813/10000000000 : ℝ)|=(4526332813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3131123053/5000000000 : ℝ)|^77 ≤ (6923464305833/12500000000000 : ℝ)^61
        have hw : |(-3131123053/5000000000 : ℝ)|=(3131123053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s2_s2_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5087070429/10000000000 : ℝ)*x 0 + (5067019049/10000000000 : ℝ)*x 1 + (2224683087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5087070429/10000000000 : ℝ)^77 ≤ (42606482854563/100000000000000 : ℝ)^61 := by
    have hnat : (5087070429 : ℕ)^77*100000000000000^61 ≤ 42606482854563^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5087070429 10000000000 42606482854563 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5067019049/10000000000 : ℝ)^77 ≤ (42394603659839/100000000000000 : ℝ)^61 := by
    have hnat : (5067019049 : ℕ)^77*100000000000000^61 ≤ 42394603659839^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5067019049 10000000000 42394603659839 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2224683087/10000000000 : ℝ)^77 ≤ (7499456738449/50000000000000 : ℝ)^61 := by
    have hnat : (2224683087 : ℕ)^77*50000000000000^61 ≤ 7499456738449^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224683087 10000000000 7499456738449 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5087070429/10000000000 : ℝ), (5067019049/10000000000 : ℝ), (2224683087/10000000000 : ℝ)] ![(42606482854563/100000000000000 : ℝ), (42394603659839/100000000000000 : ℝ), (7499456738449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5087070429/10000000000 : ℝ)|^77 ≤ (42606482854563/100000000000000 : ℝ)^61
        have hw : |(5087070429/10000000000 : ℝ)|=(5087070429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5067019049/10000000000 : ℝ)|^77 ≤ (42394603659839/100000000000000 : ℝ)^61
        have hw : |(5067019049/10000000000 : ℝ)|=(5067019049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2224683087/10000000000 : ℝ)|^77 ≤ (7499456738449/50000000000000 : ℝ)^61
        have hw : |(2224683087/10000000000 : ℝ)|=(2224683087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s2_s2_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1281975163/2500000000 : ℝ)*x 0 + (5111136271/10000000000 : ℝ)*x 1 + (-2118422813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1281975163/2500000000 : ℝ)^77 ≤ (43038605063707/100000000000000 : ℝ)^61 := by
    have hnat : (1281975163 : ℕ)^77*100000000000000^61 ≤ 43038605063707^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281975163 2500000000 43038605063707 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5111136271/10000000000 : ℝ)^77 ≤ (535763393083/1250000000000 : ℝ)^61 := by
    have hnat : (5111136271 : ℕ)^77*1250000000000^61 ≤ 535763393083^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5111136271 10000000000 535763393083 1250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118422813/10000000000 : ℝ)^77 ≤ (14100323478883/100000000000000 : ℝ)^61 := by
    have hnat : (2118422813 : ℕ)^77*100000000000000^61 ≤ 14100323478883^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118422813 10000000000 14100323478883 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1281975163/2500000000 : ℝ), (5111136271/10000000000 : ℝ), (-2118422813/10000000000 : ℝ)] ![(43038605063707/100000000000000 : ℝ), (535763393083/1250000000000 : ℝ), (14100323478883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1281975163/2500000000 : ℝ)|^77 ≤ (43038605063707/100000000000000 : ℝ)^61
        have hw : |(1281975163/2500000000 : ℝ)|=(1281975163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5111136271/10000000000 : ℝ)|^77 ≤ (535763393083/1250000000000 : ℝ)^61
        have hw : |(5111136271/10000000000 : ℝ)|=(5111136271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2118422813/10000000000 : ℝ)|^77 ≤ (14100323478883/100000000000000 : ℝ)^61
        have hw : |(-2118422813/10000000000 : ℝ)|=(2118422813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s2_s2_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1280408799/10000000000 : ℝ)*x 0 + (1078940349/2500000000 : ℝ)*x 1 + (-3243613609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1280408799/10000000000 : ℝ)^77 ≤ (3734054009193/50000000000000 : ℝ)^61 := by
    have hnat : (1280408799 : ℕ)^77*50000000000000^61 ≤ 3734054009193^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280408799 10000000000 3734054009193 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078940349/2500000000 : ℝ)^77 ≤ (34620615415713/100000000000000 : ℝ)^61 := by
    have hnat : (1078940349 : ℕ)^77*100000000000000^61 ≤ 34620615415713^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078940349 2500000000 34620615415713 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3243613609/5000000000 : ℝ)^77 ≤ (90486369611/156250000000 : ℝ)^61 := by
    have hnat : (3243613609 : ℕ)^77*156250000000^61 ≤ 90486369611^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3243613609 5000000000 90486369611 156250000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1280408799/10000000000 : ℝ), (1078940349/2500000000 : ℝ), (-3243613609/5000000000 : ℝ)] ![(3734054009193/50000000000000 : ℝ), (34620615415713/100000000000000 : ℝ), (90486369611/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1280408799/10000000000 : ℝ)|^77 ≤ (3734054009193/50000000000000 : ℝ)^61
        have hw : |(-1280408799/10000000000 : ℝ)|=(1280408799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078940349/2500000000 : ℝ)|^77 ≤ (34620615415713/100000000000000 : ℝ)^61
        have hw : |(1078940349/2500000000 : ℝ)|=(1078940349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3243613609/5000000000 : ℝ)|^77 ≤ (90486369611/156250000000 : ℝ)^61
        have hw : |(-3243613609/5000000000 : ℝ)|=(3243613609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s2_s2_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (168150159/312500000 : ℝ)*x 0 + (-1884746003/10000000000 : ℝ)*x 1 + (-629872309/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168150159/312500000 : ℝ)^77 ≤ (11433779943977/25000000000000 : ℝ)^61 := by
    have hnat : (168150159 : ℕ)^77*25000000000000^61 ≤ 11433779943977^61*312500000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168150159 312500000 11433779943977 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1884746003/10000000000 : ℝ)^77 ≤ (243324146411/2000000000000 : ℝ)^61 := by
    have hnat : (1884746003 : ℕ)^77*2000000000000^61 ≤ 243324146411^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884746003 10000000000 243324146411 2000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (629872309/1250000000 : ℝ)^77 ≤ (42098672879533/100000000000000 : ℝ)^61 := by
    have hnat : (629872309 : ℕ)^77*100000000000000^61 ≤ 42098672879533^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629872309 1250000000 42098672879533 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168150159/312500000 : ℝ), (-1884746003/10000000000 : ℝ), (-629872309/1250000000 : ℝ)] ![(11433779943977/25000000000000 : ℝ), (243324146411/2000000000000 : ℝ), (42098672879533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168150159/312500000 : ℝ)|^77 ≤ (11433779943977/25000000000000 : ℝ)^61
        have hw : |(168150159/312500000 : ℝ)|=(168150159/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1884746003/10000000000 : ℝ)|^77 ≤ (243324146411/2000000000000 : ℝ)^61
        have hw : |(-1884746003/10000000000 : ℝ)|=(1884746003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-629872309/1250000000 : ℝ)|^77 ≤ (42098672879533/100000000000000 : ℝ)^61
        have hw : |(-629872309/1250000000 : ℝ)|=(629872309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s2_s2_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2476556001/5000000000 : ℝ)*x 0 + (1384469531/2500000000 : ℝ)*x 1 + (893675699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2476556001/5000000000 : ℝ)^77 ≤ (20597579693893/50000000000000 : ℝ)^61 := by
    have hnat : (2476556001 : ℕ)^77*50000000000000^61 ≤ 20597579693893^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2476556001 5000000000 20597579693893 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1384469531/2500000000 : ℝ)^77 ≤ (23713389371677/50000000000000 : ℝ)^61 := by
    have hnat : (1384469531 : ℕ)^77*50000000000000^61 ≤ 23713389371677^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384469531 2500000000 23713389371677 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (893675699/5000000000 : ℝ)^77 ≤ (1137806185467/10000000000000 : ℝ)^61 := by
    have hnat : (893675699 : ℕ)^77*10000000000000^61 ≤ 1137806185467^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893675699 5000000000 1137806185467 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2476556001/5000000000 : ℝ), (1384469531/2500000000 : ℝ), (893675699/5000000000 : ℝ)] ![(20597579693893/50000000000000 : ℝ), (23713389371677/50000000000000 : ℝ), (1137806185467/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2476556001/5000000000 : ℝ)|^77 ≤ (20597579693893/50000000000000 : ℝ)^61
        have hw : |(2476556001/5000000000 : ℝ)|=(2476556001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1384469531/2500000000 : ℝ)|^77 ≤ (23713389371677/50000000000000 : ℝ)^61
        have hw : |(1384469531/2500000000 : ℝ)|=(1384469531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(893675699/5000000000 : ℝ)|^77 ≤ (1137806185467/10000000000000 : ℝ)^61
        have hw : |(893675699/5000000000 : ℝ)|=(893675699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s2_s2_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (317502229/625000000 : ℝ)*x 0 + (2787782397/5000000000 : ℝ)*x 1 + (-1566533569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (317502229/625000000 : ℝ)^77 ≤ (42532122813457/100000000000000 : ℝ)^61 := by
    have hnat : (317502229 : ℕ)^77*100000000000000^61 ≤ 42532122813457^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317502229 625000000 42532122813457 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2787782397/5000000000 : ℝ)^77 ≤ (2989659320151/6250000000000 : ℝ)^61 := by
    have hnat : (2787782397 : ℕ)^77*6250000000000^61 ≤ 2989659320151^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2787782397 5000000000 2989659320151 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1566533569/10000000000 : ℝ)^77 ≤ (2408332012633/25000000000000 : ℝ)^61 := by
    have hnat : (1566533569 : ℕ)^77*25000000000000^61 ≤ 2408332012633^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1566533569 10000000000 2408332012633 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(317502229/625000000 : ℝ), (2787782397/5000000000 : ℝ), (-1566533569/10000000000 : ℝ)] ![(42532122813457/100000000000000 : ℝ), (2989659320151/6250000000000 : ℝ), (2408332012633/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(317502229/625000000 : ℝ)|^77 ≤ (42532122813457/100000000000000 : ℝ)^61
        have hw : |(317502229/625000000 : ℝ)|=(317502229/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2787782397/5000000000 : ℝ)|^77 ≤ (2989659320151/6250000000000 : ℝ)^61
        have hw : |(2787782397/5000000000 : ℝ)|=(2787782397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1566533569/10000000000 : ℝ)|^77 ≤ (2408332012633/25000000000000 : ℝ)^61
        have hw : |(-1566533569/10000000000 : ℝ)|=(1566533569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s2_s2_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1006105579/10000000000 : ℝ)*x 0 + (4538937941/10000000000 : ℝ)*x 1 + (-6459210809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006105579/10000000000 : ℝ)^77 ≤ (2754303992617/50000000000000 : ℝ)^61 := by
    have hnat : (1006105579 : ℕ)^77*50000000000000^61 ≤ 2754303992617^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006105579 10000000000 2754303992617 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4538937941/10000000000 : ℝ)^77 ≤ (2305977405899/6250000000000 : ℝ)^61 := by
    have hnat : (4538937941 : ℕ)^77*6250000000000^61 ≤ 2305977405899^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538937941 10000000000 2305977405899 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6459210809/10000000000 : ℝ)^77 ≤ (11519150702249/20000000000000 : ℝ)^61 := by
    have hnat : (6459210809 : ℕ)^77*20000000000000^61 ≤ 11519150702249^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6459210809 10000000000 11519150702249 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1006105579/10000000000 : ℝ), (4538937941/10000000000 : ℝ), (-6459210809/10000000000 : ℝ)] ![(2754303992617/50000000000000 : ℝ), (2305977405899/6250000000000 : ℝ), (11519150702249/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1006105579/10000000000 : ℝ)|^77 ≤ (2754303992617/50000000000000 : ℝ)^61
        have hw : |(-1006105579/10000000000 : ℝ)|=(1006105579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4538937941/10000000000 : ℝ)|^77 ≤ (2305977405899/6250000000000 : ℝ)^61
        have hw : |(4538937941/10000000000 : ℝ)|=(4538937941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6459210809/10000000000 : ℝ)|^77 ≤ (11519150702249/20000000000000 : ℝ)^61
        have hw : |(-6459210809/10000000000 : ℝ)|=(6459210809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s2_s2_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5168771217/10000000000 : ℝ)*x 0 + (-16714517/78125000 : ℝ)*x 1 + (-5053384077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168771217/10000000000 : ℝ)^77 ≤ (1086801474993/2500000000000 : ℝ)^61 := by
    have hnat : (5168771217 : ℕ)^77*2500000000000^61 ≤ 1086801474993^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168771217 10000000000 1086801474993 2500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16714517/78125000 : ℝ)^77 ≤ (14277290017079/100000000000000 : ℝ)^61 := by
    have hnat : (16714517 : ℕ)^77*100000000000000^61 ≤ 14277290017079^61*78125000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16714517 78125000 14277290017079 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5053384077/10000000000 : ℝ)^77 ≤ (1320332842771/3125000000000 : ℝ)^61 := by
    have hnat : (5053384077 : ℕ)^77*3125000000000^61 ≤ 1320332842771^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5053384077 10000000000 1320332842771 3125000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168771217/10000000000 : ℝ), (-16714517/78125000 : ℝ), (-5053384077/10000000000 : ℝ)] ![(1086801474993/2500000000000 : ℝ), (14277290017079/100000000000000 : ℝ), (1320332842771/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168771217/10000000000 : ℝ)|^77 ≤ (1086801474993/2500000000000 : ℝ)^61
        have hw : |(5168771217/10000000000 : ℝ)|=(5168771217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16714517/78125000 : ℝ)|^77 ≤ (14277290017079/100000000000000 : ℝ)^61
        have hw : |(-16714517/78125000 : ℝ)|=(16714517/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5053384077/10000000000 : ℝ)|^77 ≤ (1320332842771/3125000000000 : ℝ)^61
        have hw : |(-5053384077/10000000000 : ℝ)|=(5053384077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s2_s2_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1391830227/2500000000 : ℝ)*x 0 + (616722311/1250000000 : ℝ)*x 1 + (1772945239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1391830227/2500000000 : ℝ)^77 ≤ (47745288187387/100000000000000 : ℝ)^61 := by
    have hnat : (1391830227 : ℕ)^77*100000000000000^61 ≤ 47745288187387^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1391830227 2500000000 47745288187387 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (616722311/1250000000 : ℝ)^77 ≤ (40992289711457/100000000000000 : ℝ)^61 := by
    have hnat : (616722311 : ℕ)^77*100000000000000^61 ≤ 40992289711457^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      616722311 1250000000 40992289711457 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1772945239/10000000000 : ℝ)^77 ≤ (2252484417473/20000000000000 : ℝ)^61 := by
    have hnat : (1772945239 : ℕ)^77*20000000000000^61 ≤ 2252484417473^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772945239 10000000000 2252484417473 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1391830227/2500000000 : ℝ), (616722311/1250000000 : ℝ), (1772945239/10000000000 : ℝ)] ![(47745288187387/100000000000000 : ℝ), (40992289711457/100000000000000 : ℝ), (2252484417473/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1391830227/2500000000 : ℝ)|^77 ≤ (47745288187387/100000000000000 : ℝ)^61
        have hw : |(1391830227/2500000000 : ℝ)|=(1391830227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(616722311/1250000000 : ℝ)|^77 ≤ (40992289711457/100000000000000 : ℝ)^61
        have hw : |(616722311/1250000000 : ℝ)|=(616722311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1772945239/10000000000 : ℝ)|^77 ≤ (2252484417473/20000000000000 : ℝ)^61
        have hw : |(1772945239/10000000000 : ℝ)|=(1772945239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s2_s2_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5565862127/10000000000 : ℝ)*x 0 + (2518622147/5000000000 : ℝ)*x 1 + (-3198909/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5565862127/10000000000 : ℝ)^77 ≤ (47729496798577/100000000000000 : ℝ)^61 := by
    have hnat : (5565862127 : ℕ)^77*100000000000000^61 ≤ 47729496798577^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5565862127 10000000000 47729496798577 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2518622147/5000000000 : ℝ)^77 ≤ (42080385104901/100000000000000 : ℝ)^61 := by
    have hnat : (2518622147 : ℕ)^77*100000000000000^61 ≤ 42080385104901^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518622147 5000000000 42080385104901 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3198909/19531250 : ℝ)^77 ≤ (2547529519481/25000000000000 : ℝ)^61 := by
    have hnat : (3198909 : ℕ)^77*25000000000000^61 ≤ 2547529519481^61*19531250^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3198909 19531250 2547529519481 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5565862127/10000000000 : ℝ), (2518622147/5000000000 : ℝ), (-3198909/19531250 : ℝ)] ![(47729496798577/100000000000000 : ℝ), (42080385104901/100000000000000 : ℝ), (2547529519481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5565862127/10000000000 : ℝ)|^77 ≤ (47729496798577/100000000000000 : ℝ)^61
        have hw : |(5565862127/10000000000 : ℝ)|=(5565862127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2518622147/5000000000 : ℝ)|^77 ≤ (42080385104901/100000000000000 : ℝ)^61
        have hw : |(2518622147/5000000000 : ℝ)|=(2518622147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3198909/19531250 : ℝ)|^77 ≤ (2547529519481/25000000000000 : ℝ)^61
        have hw : |(-3198909/19531250 : ℝ)|=(3198909/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s2_s2_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-811802119/10000000000 : ℝ)*x 0 + (4968809459/10000000000 : ℝ)*x 1 + (-3088535679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (811802119/10000000000 : ℝ)^77 ≤ (525187449751/12500000000000 : ℝ)^61 := by
    have hnat : (811802119 : ℕ)^77*12500000000000^61 ≤ 525187449751^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811802119 10000000000 525187449751 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4968809459/10000000000 : ℝ)^77 ≤ (41360028219673/100000000000000 : ℝ)^61 := by
    have hnat : (4968809459 : ℕ)^77*100000000000000^61 ≤ 41360028219673^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4968809459 10000000000 41360028219673 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3088535679/5000000000 : ℝ)^77 ≤ (2177538886761/4000000000000 : ℝ)^61 := by
    have hnat : (3088535679 : ℕ)^77*4000000000000^61 ≤ 2177538886761^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3088535679 5000000000 2177538886761 4000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-811802119/10000000000 : ℝ), (4968809459/10000000000 : ℝ), (-3088535679/5000000000 : ℝ)] ![(525187449751/12500000000000 : ℝ), (41360028219673/100000000000000 : ℝ), (2177538886761/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-811802119/10000000000 : ℝ)|^77 ≤ (525187449751/12500000000000 : ℝ)^61
        have hw : |(-811802119/10000000000 : ℝ)|=(811802119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4968809459/10000000000 : ℝ)|^77 ≤ (41360028219673/100000000000000 : ℝ)^61
        have hw : |(4968809459/10000000000 : ℝ)|=(4968809459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3088535679/5000000000 : ℝ)|^77 ≤ (2177538886761/4000000000000 : ℝ)^61
        have hw : |(-3088535679/5000000000 : ℝ)|=(3088535679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s2_s2_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1502197453/2500000000 : ℝ)*x 0 + (-375689387/2000000000 : ℝ)*x 1 + (-876778893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1502197453/2500000000 : ℝ)^77 ≤ (13143285525361/25000000000000 : ℝ)^61 := by
    have hnat : (1502197453 : ℕ)^77*25000000000000^61 ≤ 13143285525361^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1502197453 2500000000 13143285525361 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375689387/2000000000 : ℝ)^77 ≤ (6057451791001/50000000000000 : ℝ)^61 := by
    have hnat : (375689387 : ℕ)^77*50000000000000^61 ≤ 6057451791001^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375689387 2000000000 6057451791001 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (876778893/2000000000 : ℝ)^77 ≤ (35311954303923/100000000000000 : ℝ)^61 := by
    have hnat : (876778893 : ℕ)^77*100000000000000^61 ≤ 35311954303923^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876778893 2000000000 35311954303923 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1502197453/2500000000 : ℝ), (-375689387/2000000000 : ℝ), (-876778893/2000000000 : ℝ)] ![(13143285525361/25000000000000 : ℝ), (6057451791001/50000000000000 : ℝ), (35311954303923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1502197453/2500000000 : ℝ)|^77 ≤ (13143285525361/25000000000000 : ℝ)^61
        have hw : |(1502197453/2500000000 : ℝ)|=(1502197453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-375689387/2000000000 : ℝ)|^77 ≤ (6057451791001/50000000000000 : ℝ)^61
        have hw : |(-375689387/2000000000 : ℝ)|=(375689387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-876778893/2000000000 : ℝ)|^77 ≤ (35311954303923/100000000000000 : ℝ)^61
        have hw : |(-876778893/2000000000 : ℝ)|=(876778893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s2_s2_23 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1013163693/2000000000 : ℝ)*x 0 + (5045489931/10000000000 : ℝ)*x 1 + (2277607537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013163693/2000000000 : ℝ)^77 ≤ (21190962140361/50000000000000 : ℝ)^61 := by
    have hnat : (1013163693 : ℕ)^77*50000000000000^61 ≤ 21190962140361^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013163693 2000000000 21190962140361 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5045489931/10000000000 : ℝ)^77 ≤ (21083677102957/50000000000000 : ℝ)^61 := by
    have hnat : (5045489931 : ℕ)^77*50000000000000^61 ≤ 21083677102957^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5045489931 10000000000 21083677102957 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2277607537/10000000000 : ℝ)^77 ≤ (7725360750117/50000000000000 : ℝ)^61 := by
    have hnat : (2277607537 : ℕ)^77*50000000000000^61 ≤ 7725360750117^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277607537 10000000000 7725360750117 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1013163693/2000000000 : ℝ), (5045489931/10000000000 : ℝ), (2277607537/10000000000 : ℝ)] ![(21190962140361/50000000000000 : ℝ), (21083677102957/50000000000000 : ℝ), (7725360750117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1013163693/2000000000 : ℝ)|^77 ≤ (21190962140361/50000000000000 : ℝ)^61
        have hw : |(1013163693/2000000000 : ℝ)|=(1013163693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5045489931/10000000000 : ℝ)|^77 ≤ (21083677102957/50000000000000 : ℝ)^61
        have hw : |(5045489931/10000000000 : ℝ)|=(5045489931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2277607537/10000000000 : ℝ)|^77 ≤ (7725360750117/50000000000000 : ℝ)^61
        have hw : |(2277607537/10000000000 : ℝ)|=(2277607537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s2_s2_27 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1299705383/2500000000 : ℝ)*x 0 + (2591347999/5000000000 : ℝ)*x 1 + (-1936415109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299705383/2500000000 : ℝ)^77 ≤ (43791332855893/100000000000000 : ℝ)^61 := by
    have hnat : (1299705383 : ℕ)^77*100000000000000^61 ≤ 43791332855893^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299705383 2500000000 43791332855893 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591347999/5000000000 : ℝ)^77 ≤ (21809972230191/50000000000000 : ℝ)^61 := by
    have hnat : (2591347999 : ℕ)^77*50000000000000^61 ≤ 21809972230191^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591347999 5000000000 21809972230191 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1936415109/10000000000 : ℝ)^77 ≤ (6294361331627/50000000000000 : ℝ)^61 := by
    have hnat : (1936415109 : ℕ)^77*50000000000000^61 ≤ 6294361331627^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936415109 10000000000 6294361331627 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299705383/2500000000 : ℝ), (2591347999/5000000000 : ℝ), (-1936415109/10000000000 : ℝ)] ![(43791332855893/100000000000000 : ℝ), (21809972230191/50000000000000 : ℝ), (6294361331627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299705383/2500000000 : ℝ)|^77 ≤ (43791332855893/100000000000000 : ℝ)^61
        have hw : |(1299705383/2500000000 : ℝ)|=(1299705383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591347999/5000000000 : ℝ)|^77 ≤ (21809972230191/50000000000000 : ℝ)^61
        have hw : |(2591347999/5000000000 : ℝ)|=(2591347999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1936415109/10000000000 : ℝ)|^77 ≤ (6294361331627/50000000000000 : ℝ)^61
        have hw : |(-1936415109/10000000000 : ℝ)|=(1936415109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316054_s2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((6401/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6401/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(54153/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(54153/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42163/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42163/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6161/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6161/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3269/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3269/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-508/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-508/3125 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s2_pow0 : (6401/12500 : ℝ) ^ (19/4 : ℝ) ≤ (1625977951046661/39062500000000000 : ℝ) := by
    have hpowers : (6401/12500 : ℝ)^19 ≤ (1625977951046661/39062500000000000 : ℝ)^4 := by
      have hnat : (6401 : ℕ)^19*39062500000000000^4 ≤ 1625977951046661^4*12500^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6401 12500 1625977951046661 39062500000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6401/12500 : ℝ)) (X := (1625977951046661/39062500000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s2_corner0a : (40688477951046661/39062500000000000 : ℝ) ≤ (10086226528177947/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (40688477951046661/39062500000000000 : ℝ)^4 ≤ (10086226528177947/10000000000000000 : ℝ)^19 := by
      have hnat : (40688477951046661 : ℕ)^4*10000000000000000^19 ≤ 10086226528177947^19*39062500000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40688477951046661 39062500000000000 10086226528177947 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10086226528177947/10000000000000000 : ℝ)) (X := (40688477951046661/39062500000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s2_corner0b : (21157227951046661/19531250000000000 : ℝ) ≤ (1016977420967009/1000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (21157227951046661/19531250000000000 : ℝ)^4 ≤ (1016977420967009/1000000000000000 : ℝ)^19 := by
      have hnat : (21157227951046661 : ℕ)^4*1000000000000000^19 ≤ 1016977420967009^19*19531250000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21157227951046661 19531250000000000 1016977420967009 1000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1016977420967009/1000000000000000 : ℝ)) (X := (21157227951046661/19531250000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(86226528177947/5120800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(83547681492143/5120800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (6401/12500 : ℝ)) (alpha := (86226528177947/5120800000000000 : ℝ)) (beta := (83547681492143/5120800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (6401/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(86226528177947/5120800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(83547681492143/5120800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (54153/100000 : ℝ) ^ (19/4 : ℝ) ≤ (339302447032073989/6250000000000000000 : ℝ) := by
    have hpowers : (54153/100000 : ℝ)^19 ≤ (339302447032073989/6250000000000000000 : ℝ)^4 := by
      have hnat : (54153 : ℕ)^19*6250000000000000000^4 ≤ 339302447032073989^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54153 100000 339302447032073989 6250000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (54153/100000 : ℝ)) (X := (339302447032073989/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s2_corner1a : (6589302447032073989/6250000000000000000 : ℝ) ≤ (5055959278598367/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (6589302447032073989/6250000000000000000 : ℝ)^4 ≤ (5055959278598367/5000000000000000 : ℝ)^19 := by
      have hnat : (6589302447032073989 : ℕ)^4*5000000000000000^19 ≤ 5055959278598367^19*6250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6589302447032073989 6250000000000000000 5055959278598367 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5055959278598367/5000000000000000 : ℝ)) (X := (6589302447032073989/6250000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s2_corner1b : (3464302447032073989/3125000000000000000 : ℝ) ≤ (2043875181781859/2000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3464302447032073989/3125000000000000000 : ℝ)^4 ≤ (2043875181781859/2000000000000000 : ℝ)^19 := by
      have hnat : (3464302447032073989 : ℕ)^4*2000000000000000^19 ≤ 2043875181781859^19*3125000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3464302447032073989 3125000000000000000 2043875181781859 2000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2043875181781859/2000000000000000 : ℝ)) (X := (3464302447032073989/3125000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(55959278598367/2707650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(107457351712561/5415300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (54153/100000 : ℝ)) (alpha := (55959278598367/2707650000000000 : ℝ)) (beta := (107457351712561/5415300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (54153/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(55959278598367/2707650000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(107457351712561/5415300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (42163/100000 : ℝ) ^ (19/4 : ℝ) ≤ (413394462272892851/25000000000000000000 : ℝ) := by
    have hpowers : (42163/100000 : ℝ)^19 ≤ (413394462272892851/25000000000000000000 : ℝ)^4 := by
      have hnat : (42163 : ℕ)^19*25000000000000000000^4 ≤ 413394462272892851^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42163 100000 413394462272892851 25000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42163/100000 : ℝ)) (X := (413394462272892851/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s2_corner2a : (25413394462272892851/25000000000000000000 : ℝ) ≤ (10034587152193417/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (25413394462272892851/25000000000000000000 : ℝ)^4 ≤ (10034587152193417/10000000000000000 : ℝ)^19 := by
      have hnat : (25413394462272892851 : ℕ)^4*10000000000000000^19 ≤ 10034587152193417^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25413394462272892851 25000000000000000000 10034587152193417 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10034587152193417/10000000000000000 : ℝ)) (X := (25413394462272892851/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s2_corner2b : (12913394462272892851/12500000000000000000 : ℝ) ≤ (10068732941999733/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (12913394462272892851/12500000000000000000 : ℝ)^4 ≤ (10068732941999733/10000000000000000 : ℝ)^19 := by
      have hnat : (12913394462272892851 : ℕ)^4*10000000000000000^19 ≤ 10068732941999733^19*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12913394462272892851 12500000000000000000 10068732941999733 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10068732941999733/10000000000000000 : ℝ)) (X := (12913394462272892851/12500000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(34587152193417/4216300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(8536447451579/1054075000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (42163/100000 : ℝ)) (alpha := (34587152193417/4216300000000000 : ℝ)) (beta := (8536447451579/1054075000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (42163/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(34587152193417/4216300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(8536447451579/1054075000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-166432869/1250000000 : ℝ)*X 0 0+(4526332813/10000000000 : ℝ)*X 0 1+(-3131123053/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5087070429/10000000000 : ℝ)*X 2 0+(5067019049/10000000000 : ℝ)*X 2 1+(2224683087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((1281975163/2500000000 : ℝ)*X 0 0+(5111136271/10000000000 : ℝ)*X 0 1+(-2118422813/10000000000 : ℝ)*X 0 2+(1281975163/2500000000 : ℝ)*X 1 0+(5111136271/10000000000 : ℝ)*X 1 1+(-2118422813/10000000000 : ℝ)*X 1 2+(1281975163/2500000000 : ℝ)*X 2 0+(5111136271/10000000000 : ℝ)*X 2 1+(-2118422813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1280408799/10000000000 : ℝ)*X 0 0+(1078940349/2500000000 : ℝ)*X 0 1+(-3243613609/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((168150159/312500000 : ℝ)*X 1 0+(-1884746003/10000000000 : ℝ)*X 1 1+(-629872309/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2476556001/5000000000 : ℝ)*X 2 0+(1384469531/2500000000 : ℝ)*X 2 1+(893675699/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((317502229/625000000 : ℝ)*X 0 0+(2787782397/5000000000 : ℝ)*X 0 1+(-1566533569/10000000000 : ℝ)*X 0 2+(317502229/625000000 : ℝ)*X 1 0+(2787782397/5000000000 : ℝ)*X 1 1+(-1566533569/10000000000 : ℝ)*X 1 2+(317502229/625000000 : ℝ)*X 2 0+(2787782397/5000000000 : ℝ)*X 2 1+(-1566533569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1006105579/10000000000 : ℝ)*X 0 0+(4538937941/10000000000 : ℝ)*X 0 1+(-6459210809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((5168771217/10000000000 : ℝ)*X 1 0+(-16714517/78125000 : ℝ)*X 1 1+(-5053384077/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1391830227/2500000000 : ℝ)*X 2 0+(616722311/1250000000 : ℝ)*X 2 1+(1772945239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((5565862127/10000000000 : ℝ)*X 0 0+(2518622147/5000000000 : ℝ)*X 0 1+(-3198909/19531250 : ℝ)*X 0 2+(5565862127/10000000000 : ℝ)*X 1 0+(2518622147/5000000000 : ℝ)*X 1 1+(-3198909/19531250 : ℝ)*X 1 2+(5565862127/10000000000 : ℝ)*X 2 0+(2518622147/5000000000 : ℝ)*X 2 1+(-3198909/19531250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-811802119/10000000000 : ℝ)*X 0 0+(4968809459/10000000000 : ℝ)*X 0 1+(-3088535679/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1502197453/2500000000 : ℝ)*X 1 0+(-375689387/2000000000 : ℝ)*X 1 1+(-876778893/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1013163693/2000000000 : ℝ)*X 2 0+(5045489931/10000000000 : ℝ)*X 2 1+(2277607537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1299705383/2500000000 : ℝ)*X 0 0+(2591347999/5000000000 : ℝ)*X 0 1+(-1936415109/10000000000 : ℝ)*X 0 2+(1299705383/2500000000 : ℝ)*X 1 0+(2591347999/5000000000 : ℝ)*X 1 1+(-1936415109/10000000000 : ℝ)*X 1 2+(1299705383/2500000000 : ℝ)*X 2 0+(2591347999/5000000000 : ℝ)*X 2 1+(-1936415109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((6161/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6161/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (343591611604186629866684747/23108890200000000000000000000000 : ℝ) := by norm_num
    linear_combination (462481243673/250000000000 : ℝ)*(base39) + (69093/10000000000 : ℝ)*(base50) + (795520936117/1000000000000 : ℝ)*(base60) + (10768649704471/1000000000000 : ℝ)*(major_s2_0) + (10768649704471/1000000000000 : ℝ)*(major_s2_1) + (10768649704471/1000000000000 : ℝ)*(major_s2_2) + (58688123/500000000000 : ℝ)*(sp_s2_0) + (1546187783519/100000000000 : ℝ)*(sp_s2_7) + (3092350720773/200000000000 : ℝ)*(sp_s2_8) + (3865487642379/250000000000 : ℝ)*(sp_s2_9) + (1215032377223/200000000000 : ℝ)*(sp_s2_13) + (137355259/1000000000000 : ℝ)*(sp_s2_14) + (37896283/100000000000 : ℝ)*(sp_s2_15) + (9099859/50000000000 : ℝ)*(sp_s2_23) + (1215032377223/200000000000 : ℝ)*(f.failure) + (1932766570837/125000000000 : ℝ)*(f.sum) + (5689760944057260107/20756844900000000000000000000000 : ℝ)*base62 + (435941977201813/2108150000000000000000000000 : ℝ)*base65 + (4501099939733371/5415300000000000000000000000 : ℝ)*base66 + (2445839626485707/4216300000000000000000000000 : ℝ)*base69 + (56723955507066303481/215908290400000000000000000000000 : ℝ)*base70 + (2667785241798647/5120800000000000000000000000 : ℝ)*base72 + (1239351819436523/2707650000000000000000000000 : ℝ)*base74 + (508074421816883/5120800000000000000000000000 : ℝ)*base76 + (161220387525679556359/277306682400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (2689/20000000000000000 : ℝ)*base86 + (2689/20000000000000000 : ℝ)*base88 + (2689/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3269/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3269/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28037564677653795374560627/1729737075000000000000000000000 : ℝ) := by norm_num
    linear_combination (1787188725271/1000000000000 : ℝ)*(base39) + (7327229/1000000000000 : ℝ)*(base40) + (103443049853/200000000000 : ℝ)*(base60) + (5392931472019/500000000000 : ℝ)*(major_s2_0) + (5392931472019/500000000000 : ℝ)*(major_s2_1) + (5392931472019/500000000000 : ℝ)*(major_s2_2) + (10746809/250000000000 : ℝ)*(sp_s2_6) + (279099451/1000000000000 : ℝ)*(sp_s2_7) + (240791697/1000000000000 : ℝ)*(sp_s2_8) + (15486568605347/1000000000000 : ℝ)*(sp_s2_14) + (15486606913101/1000000000000 : ℝ)*(sp_s2_15) + (15486767101247/1000000000000 : ℝ)*(sp_s2_16) + (6084829792987/1000000000000 : ℝ)*(sp_s2_20) + (80603551/1000000000000 : ℝ)*(sp_s2_23) + (3042436390111/500000000000 : ℝ)*(f.failure) + (7743423852399/500000000000 : ℝ)*(f.sum) + (673450517705110501/1297302806250000000000000000000 : ℝ)*base62 + (1771952628812451/2108150000000000000000000000 : ℝ)*base64 + (1007077266663583/1353825000000000000000000000 : ℝ)*base67 + (2311226362862387/2108150000000000000000000000 : ℝ)*base68 + (4728713664311863851/107954145200000000000000000000000 : ℝ)*base71 + (388918906459717/2560400000000000000000000000 : ℝ)*base73 + (1362890001964367/1353825000000000000000000000 : ℝ)*base74 + (1671917776197047/2560400000000000000000000000 : ℝ)*base76 + (58017521966465787091/138653341200000000000000000000000 : ℝ)*base78 + (5527/50000000000000000 : ℝ)*base87 + (5527/50000000000000000 : ℝ)*base89 + (5527/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-508/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-508/3125 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (215136465370441318100505789/53977072600000000000000000000000 : ℝ) := by norm_num
    linear_combination (1520119891581/1000000000000 : ℝ)*(base39) + (8627/10000000000 : ℝ)*(base40) + (83009/100000000000 : ℝ)*(base50) + (7796294681/500000000000 : ℝ)*(base60) + (6868599022737/1000000000000 : ℝ)*(major_s2_0) + (6868599022737/1000000000000 : ℝ)*(major_s2_1) + (6868599022737/1000000000000 : ℝ)*(major_s2_2) + (121154789/500000000000 : ℝ)*(sp_s2_2) + (19080677/500000000000 : ℝ)*(sp_s2_13) + (40423933/1000000000000 : ℝ)*(sp_s2_20) + (4931129309913/500000000000 : ℝ)*(sp_s2_21) + (4931129309913/500000000000 : ℝ)*(sp_s2_22) + (1232752038781/125000000000 : ℝ)*(sp_s2_23) + (3874859511791/1000000000000 : ℝ)*(sp_s2_27) + (1937469048539/500000000000 : ℝ)*(f.failure) + (4931129309913/500000000000 : ℝ)*(f.sum) + (114439899758021759/2306316100000000000000000000000 : ℝ)*base63 + (25659374047797/65879687500000000000000000 : ℝ)*base64 + (243455719869617/601700000000000000000000000 : ℝ)*base67 + (1340899072143401/4216300000000000000000000000 : ℝ)*base68 + (70958707274214576847/215908290400000000000000000000000 : ℝ)*base70 + (359193249984689/5120800000000000000000000000 : ℝ)*base72 + (33160351218327/150425000000000000000000000 : ℝ)*base74 + (2699245466971541/5120800000000000000000000000 : ℝ)*base76 + (5664827048630676217/30811853600000000000000000000000 : ℝ)*base78 + (27523/50000000000000000 : ℝ)*base87 + (27523/50000000000000000 : ℝ)*base89 + (27523/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((6401/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6401/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(54153/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(54153/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42163/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42163/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6161/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6161/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3269/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3269/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-508/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-508/3125 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c316054_s2 p hpa hpb X hX hprev1

#print axioms solution

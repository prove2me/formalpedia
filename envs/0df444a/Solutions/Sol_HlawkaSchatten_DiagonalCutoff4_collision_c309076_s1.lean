-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309076_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:06:05.070958+00:00
-- url     : https://prove2.me/submissions/3869fac7-d036-4701-882f-b3eb69aa0852

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
theorem collision_support_c309076_s1_s1_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-57696903/400000000 : ℝ)*x 0 + (-6271489063/10000000000 : ℝ)*x 1 + (2334385999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (57696903/400000000 : ℝ)^35 ≤ (4063541884587/50000000000000 : ℝ)^27 := by
    have hnat : (57696903 : ℕ)^35*50000000000000^27 ≤ 4063541884587^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57696903 400000000 4063541884587 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6271489063/10000000000 : ℝ)^35 ≤ (27308783430587/50000000000000 : ℝ)^27 := by
    have hnat : (6271489063 : ℕ)^35*50000000000000^27 ≤ 27308783430587^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6271489063 10000000000 27308783430587 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2334385999/5000000000 : ℝ)^35 ≤ (3725534936549/10000000000000 : ℝ)^27 := by
    have hnat : (2334385999 : ℕ)^35*10000000000000^27 ≤ 3725534936549^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2334385999 5000000000 3725534936549 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-57696903/400000000 : ℝ), (-6271489063/10000000000 : ℝ), (2334385999/5000000000 : ℝ)] ![(4063541884587/50000000000000 : ℝ), (27308783430587/50000000000000 : ℝ), (3725534936549/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-57696903/400000000 : ℝ)|^35 ≤ (4063541884587/50000000000000 : ℝ)^27
        have hw : |(-57696903/400000000 : ℝ)|=(57696903/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6271489063/10000000000 : ℝ)|^35 ≤ (27308783430587/50000000000000 : ℝ)^27
        have hw : |(-6271489063/10000000000 : ℝ)|=(6271489063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2334385999/5000000000 : ℝ)|^35 ≤ (3725534936549/10000000000000 : ℝ)^27
        have hw : |(2334385999/5000000000 : ℝ)|=(2334385999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309076_s1_s1_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6395171679/10000000000 : ℝ)*x 0 + (52245897/156250000 : ℝ)*x 1 + (717106827/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6395171679/10000000000 : ℝ)^35 ≤ (7002239303979/12500000000000 : ℝ)^27 := by
    have hnat : (6395171679 : ℕ)^35*12500000000000^27 ≤ 7002239303979^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6395171679 10000000000 7002239303979 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52245897/156250000 : ℝ)^35 ≤ (3021161413033/12500000000000 : ℝ)^27 := by
    have hnat : (52245897 : ℕ)^35*12500000000000^27 ≤ 3021161413033^27*156250000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52245897 156250000 3021161413033 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (717106827/2500000000 : ℝ)^35 ≤ (9906397122539/50000000000000 : ℝ)^27 := by
    have hnat : (717106827 : ℕ)^35*50000000000000^27 ≤ 9906397122539^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      717106827 2500000000 9906397122539 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6395171679/10000000000 : ℝ), (52245897/156250000 : ℝ), (717106827/2500000000 : ℝ)] ![(7002239303979/12500000000000 : ℝ), (3021161413033/12500000000000 : ℝ), (9906397122539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6395171679/10000000000 : ℝ)|^35 ≤ (7002239303979/12500000000000 : ℝ)^27
        have hw : |(6395171679/10000000000 : ℝ)|=(6395171679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52245897/156250000 : ℝ)|^35 ≤ (3021161413033/12500000000000 : ℝ)^27
        have hw : |(52245897/156250000 : ℝ)|=(52245897/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(717106827/2500000000 : ℝ)|^35 ≤ (9906397122539/50000000000000 : ℝ)^27
        have hw : |(717106827/2500000000 : ℝ)|=(717106827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309076_s1_s1_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1187096217/2500000000 : ℝ)*x 0 + (-2298912107/5000000000 : ℝ)*x 1 + (-217119171/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1187096217/2500000000 : ℝ)^35 ≤ (38080940353729/100000000000000 : ℝ)^27 := by
    have hnat : (1187096217 : ℕ)^35*100000000000000^27 ≤ 38080940353729^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187096217 2500000000 38080940353729 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2298912107/5000000000 : ℝ)^35 ≤ (7304624133087/20000000000000 : ℝ)^27 := by
    have hnat : (2298912107 : ℕ)^35*20000000000000^27 ≤ 7304624133087^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2298912107 5000000000 7304624133087 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217119171/625000000 : ℝ)^35 ≤ (25395938967447/100000000000000 : ℝ)^27 := by
    have hnat : (217119171 : ℕ)^35*100000000000000^27 ≤ 25395938967447^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217119171 625000000 25395938967447 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1187096217/2500000000 : ℝ), (-2298912107/5000000000 : ℝ), (-217119171/625000000 : ℝ)] ![(38080940353729/100000000000000 : ℝ), (7304624133087/20000000000000 : ℝ), (25395938967447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1187096217/2500000000 : ℝ)|^35 ≤ (38080940353729/100000000000000 : ℝ)^27
        have hw : |(1187096217/2500000000 : ℝ)|=(1187096217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2298912107/5000000000 : ℝ)|^35 ≤ (7304624133087/20000000000000 : ℝ)^27
        have hw : |(-2298912107/5000000000 : ℝ)|=(2298912107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-217119171/625000000 : ℝ)|^35 ≤ (25395938967447/100000000000000 : ℝ)^27
        have hw : |(-217119171/625000000 : ℝ)|=(217119171/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309076_s1_s1_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2630661/19531250 : ℝ)*x 0 + (-919439549/1250000000 : ℝ)*x 1 + (1737519499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630661/19531250 : ℝ)^35 ≤ (1487270565571/20000000000000 : ℝ)^27 := by
    have hnat : (2630661 : ℕ)^35*20000000000000^27 ≤ 1487270565571^27*19531250^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630661 19531250 1487270565571 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (919439549/1250000000 : ℝ)^35 ≤ (16789244430131/25000000000000 : ℝ)^27 := by
    have hnat : (919439549 : ℕ)^35*25000000000000^27 ≤ 16789244430131^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919439549 1250000000 16789244430131 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1737519499/5000000000 : ℝ)^35 ≤ (6351667356619/25000000000000 : ℝ)^27 := by
    have hnat : (1737519499 : ℕ)^35*25000000000000^27 ≤ 6351667356619^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737519499 5000000000 6351667356619 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2630661/19531250 : ℝ), (-919439549/1250000000 : ℝ), (1737519499/5000000000 : ℝ)] ![(1487270565571/20000000000000 : ℝ), (16789244430131/25000000000000 : ℝ), (6351667356619/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2630661/19531250 : ℝ)|^35 ≤ (1487270565571/20000000000000 : ℝ)^27
        have hw : |(-2630661/19531250 : ℝ)|=(2630661/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-919439549/1250000000 : ℝ)|^35 ≤ (16789244430131/25000000000000 : ℝ)^27
        have hw : |(-919439549/1250000000 : ℝ)|=(919439549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1737519499/5000000000 : ℝ)|^35 ≤ (6351667356619/25000000000000 : ℝ)^27
        have hw : |(1737519499/5000000000 : ℝ)|=(1737519499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309076_s1_s1_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5510257479/10000000000 : ℝ)*x 0 + (1021270017/2500000000 : ℝ)*x 1 + (3162410029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510257479/10000000000 : ℝ)^35 ≤ (46182993865149/100000000000000 : ℝ)^27 := by
    have hnat : (5510257479 : ℕ)^35*100000000000000^27 ≤ 46182993865149^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510257479 10000000000 46182993865149 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021270017/2500000000 : ℝ)^35 ≤ (15666455423961/50000000000000 : ℝ)^27 := by
    have hnat : (1021270017 : ℕ)^35*50000000000000^27 ≤ 15666455423961^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021270017 2500000000 15666455423961 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3162410029/10000000000 : ℝ)^35 ≤ (5621023816299/25000000000000 : ℝ)^27 := by
    have hnat : (3162410029 : ℕ)^35*25000000000000^27 ≤ 5621023816299^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3162410029 10000000000 5621023816299 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510257479/10000000000 : ℝ), (1021270017/2500000000 : ℝ), (3162410029/10000000000 : ℝ)] ![(46182993865149/100000000000000 : ℝ), (15666455423961/50000000000000 : ℝ), (5621023816299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510257479/10000000000 : ℝ)|^35 ≤ (46182993865149/100000000000000 : ℝ)^27
        have hw : |(5510257479/10000000000 : ℝ)|=(5510257479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1021270017/2500000000 : ℝ)|^35 ≤ (15666455423961/50000000000000 : ℝ)^27
        have hw : |(1021270017/2500000000 : ℝ)|=(1021270017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3162410029/10000000000 : ℝ)|^35 ≤ (5621023816299/25000000000000 : ℝ)^27
        have hw : |(3162410029/10000000000 : ℝ)|=(3162410029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309076_s1_s1_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1204827629/2500000000 : ℝ)*x 0 + (-1318390207/2500000000 : ℝ)*x 1 + (-2612494853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1204827629/2500000000 : ℝ)^35 ≤ (19409954469507/50000000000000 : ℝ)^27 := by
    have hnat : (1204827629 : ℕ)^35*50000000000000^27 ≤ 19409954469507^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204827629 2500000000 19409954469507 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318390207/2500000000 : ℝ)^35 ≤ (4362790836413/10000000000000 : ℝ)^27 := by
    have hnat : (1318390207 : ℕ)^35*10000000000000^27 ≤ 4362790836413^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318390207 2500000000 4362790836413 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2612494853/10000000000 : ℝ)^35 ≤ (17552182685801/100000000000000 : ℝ)^27 := by
    have hnat : (2612494853 : ℕ)^35*100000000000000^27 ≤ 17552182685801^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612494853 10000000000 17552182685801 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1204827629/2500000000 : ℝ), (-1318390207/2500000000 : ℝ), (-2612494853/10000000000 : ℝ)] ![(19409954469507/50000000000000 : ℝ), (4362790836413/10000000000000 : ℝ), (17552182685801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1204827629/2500000000 : ℝ)|^35 ≤ (19409954469507/50000000000000 : ℝ)^27
        have hw : |(1204827629/2500000000 : ℝ)|=(1204827629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1318390207/2500000000 : ℝ)|^35 ≤ (4362790836413/10000000000000 : ℝ)^27
        have hw : |(-1318390207/2500000000 : ℝ)|=(1318390207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2612494853/10000000000 : ℝ)|^35 ≤ (17552182685801/100000000000000 : ℝ)^27
        have hw : |(-2612494853/10000000000 : ℝ)|=(2612494853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309076_s1_s1_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (643323631/2000000000 : ℝ)*x 0 + (40148347/10000000000 : ℝ)*x 1 + (8168840661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (643323631/2000000000 : ℝ)^35 ≤ (22984962934319/100000000000000 : ℝ)^27 := by
    have hnat : (643323631 : ℕ)^35*100000000000000^27 ≤ 22984962934319^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643323631 2000000000 22984962934319 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40148347/10000000000 : ℝ)^35 ≤ (19569660137/25000000000000 : ℝ)^27 := by
    have hnat : (40148347 : ℕ)^35*25000000000000^27 ≤ 19569660137^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40148347 10000000000 19569660137 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8168840661/10000000000 : ℝ)^35 ≤ (9617094801423/12500000000000 : ℝ)^27 := by
    have hnat : (8168840661 : ℕ)^35*12500000000000^27 ≤ 9617094801423^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8168840661 10000000000 9617094801423 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(643323631/2000000000 : ℝ), (40148347/10000000000 : ℝ), (8168840661/10000000000 : ℝ)] ![(22984962934319/100000000000000 : ℝ), (19569660137/25000000000000 : ℝ), (9617094801423/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(643323631/2000000000 : ℝ)|^35 ≤ (22984962934319/100000000000000 : ℝ)^27
        have hw : |(643323631/2000000000 : ℝ)|=(643323631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40148347/10000000000 : ℝ)|^35 ≤ (19569660137/25000000000000 : ℝ)^27
        have hw : |(40148347/10000000000 : ℝ)|=(40148347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8168840661/10000000000 : ℝ)|^35 ≤ (9617094801423/12500000000000 : ℝ)^27
        have hw : |(8168840661/10000000000 : ℝ)|=(8168840661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309076_s1_s1_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065846341/10000000000 : ℝ)*x 0 + (-2707056311/5000000000 : ℝ)*x 1 + (580120641/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065846341/10000000000 : ℝ)^35 ≤ (274520078031/5000000000000 : ℝ)^27 := by
    have hnat : (1065846341 : ℕ)^35*5000000000000^27 ≤ 274520078031^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065846341 10000000000 274520078031 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707056311/5000000000 : ℝ)^35 ≤ (4514112800141/10000000000000 : ℝ)^27 := by
    have hnat : (2707056311 : ℕ)^35*10000000000000^27 ≤ 4514112800141^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707056311 5000000000 4514112800141 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (580120641/1000000000 : ℝ)^35 ≤ (49368470418999/100000000000000 : ℝ)^27 := by
    have hnat : (580120641 : ℕ)^35*100000000000000^27 ≤ 49368470418999^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580120641 1000000000 49368470418999 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065846341/10000000000 : ℝ), (-2707056311/5000000000 : ℝ), (580120641/1000000000 : ℝ)] ![(274520078031/5000000000000 : ℝ), (4514112800141/10000000000000 : ℝ), (49368470418999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065846341/10000000000 : ℝ)|^35 ≤ (274520078031/5000000000000 : ℝ)^27
        have hw : |(-1065846341/10000000000 : ℝ)|=(1065846341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2707056311/5000000000 : ℝ)|^35 ≤ (4514112800141/10000000000000 : ℝ)^27
        have hw : |(-2707056311/5000000000 : ℝ)|=(2707056311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(580120641/1000000000 : ℝ)|^35 ≤ (49368470418999/100000000000000 : ℝ)^27
        have hw : |(580120641/1000000000 : ℝ)|=(580120641/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309076_s1_s1_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7600017907/10000000000 : ℝ)*x 0 + (1238896967/5000000000 : ℝ)*x 1 + (2139335929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7600017907/10000000000 : ℝ)^35 ≤ (1751622181681/2500000000000 : ℝ)^27 := by
    have hnat : (7600017907 : ℕ)^35*2500000000000^27 ≤ 1751622181681^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7600017907 10000000000 1751622181681 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1238896967/5000000000 : ℝ)^35 ≤ (3277622556023/20000000000000 : ℝ)^27 := by
    have hnat : (1238896967 : ℕ)^35*20000000000000^27 ≤ 3277622556023^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238896967 5000000000 3277622556023 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2139335929/10000000000 : ℝ)^35 ≤ (6773499966661/50000000000000 : ℝ)^27 := by
    have hnat : (2139335929 : ℕ)^35*50000000000000^27 ≤ 6773499966661^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139335929 10000000000 6773499966661 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7600017907/10000000000 : ℝ), (1238896967/5000000000 : ℝ), (2139335929/10000000000 : ℝ)] ![(1751622181681/2500000000000 : ℝ), (3277622556023/20000000000000 : ℝ), (6773499966661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7600017907/10000000000 : ℝ)|^35 ≤ (1751622181681/2500000000000 : ℝ)^27
        have hw : |(7600017907/10000000000 : ℝ)|=(7600017907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1238896967/5000000000 : ℝ)|^35 ≤ (3277622556023/20000000000000 : ℝ)^27
        have hw : |(1238896967/5000000000 : ℝ)|=(1238896967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2139335929/10000000000 : ℝ)|^35 ≤ (6773499966661/50000000000000 : ℝ)^27
        have hw : |(2139335929/10000000000 : ℝ)|=(2139335929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309076_s1_s1_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (359450261/625000000 : ℝ)*x 0 + (-2313865279/5000000000 : ℝ)*x 1 + (-2236640137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (359450261/625000000 : ℝ)^35 ≤ (1220439380207/2500000000000 : ℝ)^27 := by
    have hnat : (359450261 : ℕ)^35*2500000000000^27 ≤ 1220439380207^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359450261 625000000 1220439380207 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2313865279/5000000000 : ℝ)^35 ≤ (36831369027971/100000000000000 : ℝ)^27 := by
    have hnat : (2313865279 : ℕ)^35*100000000000000^27 ≤ 36831369027971^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313865279 5000000000 36831369027971 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236640137/10000000000 : ℝ)^35 ≤ (14351055753507/100000000000000 : ℝ)^27 := by
    have hnat : (2236640137 : ℕ)^35*100000000000000^27 ≤ 14351055753507^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236640137 10000000000 14351055753507 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(359450261/625000000 : ℝ), (-2313865279/5000000000 : ℝ), (-2236640137/10000000000 : ℝ)] ![(1220439380207/2500000000000 : ℝ), (36831369027971/100000000000000 : ℝ), (14351055753507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(359450261/625000000 : ℝ)|^35 ≤ (1220439380207/2500000000000 : ℝ)^27
        have hw : |(359450261/625000000 : ℝ)|=(359450261/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2313865279/5000000000 : ℝ)|^35 ≤ (36831369027971/100000000000000 : ℝ)^27
        have hw : |(-2313865279/5000000000 : ℝ)|=(2313865279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2236640137/10000000000 : ℝ)|^35 ≤ (14351055753507/100000000000000 : ℝ)^27
        have hw : |(-2236640137/10000000000 : ℝ)|=(2236640137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309076_s1_s1_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1109570837/5000000000 : ℝ)*x 0 + (-294047/10000000000 : ℝ)*x 1 + (888520569/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1109570837/5000000000 : ℝ)^35 ≤ (2841136310897/20000000000000 : ℝ)^27 := by
    have hnat : (1109570837 : ℕ)^35*20000000000000^27 ≤ 2841136310897^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109570837 5000000000 2841136310897 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (294047/10000000000 : ℝ)^35 ≤ (66787537/50000000000000 : ℝ)^27 := by
    have hnat : (294047 : ℕ)^35*50000000000000^27 ≤ 66787537^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294047 10000000000 66787537 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (888520569/1000000000 : ℝ)^35 ≤ (42897092427527/50000000000000 : ℝ)^27 := by
    have hnat : (888520569 : ℕ)^35*50000000000000^27 ≤ 42897092427527^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888520569 1000000000 42897092427527 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1109570837/5000000000 : ℝ), (-294047/10000000000 : ℝ), (888520569/1000000000 : ℝ)] ![(2841136310897/20000000000000 : ℝ), (66787537/50000000000000 : ℝ), (42897092427527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1109570837/5000000000 : ℝ)|^35 ≤ (2841136310897/20000000000000 : ℝ)^27
        have hw : |(1109570837/5000000000 : ℝ)|=(1109570837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-294047/10000000000 : ℝ)|^35 ≤ (66787537/50000000000000 : ℝ)^27
        have hw : |(-294047/10000000000 : ℝ)|=(294047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(888520569/1000000000 : ℝ)|^35 ≤ (42897092427527/50000000000000 : ℝ)^27
        have hw : |(888520569/1000000000 : ℝ)|=(888520569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309076_s1_s1_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-733526381/10000000000 : ℝ)*x 0 + (-904071919/1250000000 : ℝ)*x 1 + (1010668291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (733526381/10000000000 : ℝ)^35 ≤ (422817190327/12500000000000 : ℝ)^27 := by
    have hnat : (733526381 : ℕ)^35*12500000000000^27 ≤ 422817190327^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733526381 10000000000 422817190327 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904071919/1250000000 : ℝ)^35 ≤ (65705540813397/100000000000000 : ℝ)^27 := by
    have hnat : (904071919 : ℕ)^35*100000000000000^27 ≤ 65705540813397^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904071919 1250000000 65705540813397 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010668291/2500000000 : ℝ)^35 ≤ (30911921643669/100000000000000 : ℝ)^27 := by
    have hnat : (1010668291 : ℕ)^35*100000000000000^27 ≤ 30911921643669^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010668291 2500000000 30911921643669 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-733526381/10000000000 : ℝ), (-904071919/1250000000 : ℝ), (1010668291/2500000000 : ℝ)] ![(422817190327/12500000000000 : ℝ), (65705540813397/100000000000000 : ℝ), (30911921643669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-733526381/10000000000 : ℝ)|^35 ≤ (422817190327/12500000000000 : ℝ)^27
        have hw : |(-733526381/10000000000 : ℝ)|=(733526381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-904071919/1250000000 : ℝ)|^35 ≤ (65705540813397/100000000000000 : ℝ)^27
        have hw : |(-904071919/1250000000 : ℝ)|=(904071919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010668291/2500000000 : ℝ)|^35 ≤ (30911921643669/100000000000000 : ℝ)^27
        have hw : |(1010668291/2500000000 : ℝ)|=(1010668291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309076_s1_s1_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1823915179/2500000000 : ℝ)*x 0 + (544239493/2000000000 : ℝ)*x 1 + (1159863631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1823915179/2500000000 : ℝ)^35 ≤ (13289883728179/20000000000000 : ℝ)^27 := by
    have hnat : (1823915179 : ℕ)^35*20000000000000^27 ≤ 13289883728179^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823915179 2500000000 13289883728179 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544239493/2000000000 : ℝ)^35 ≤ (4626169755177/25000000000000 : ℝ)^27 := by
    have hnat : (544239493 : ℕ)^35*25000000000000^27 ≤ 4626169755177^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544239493 2000000000 4626169755177 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1159863631/5000000000 : ℝ)^35 ≤ (3009180464017/20000000000000 : ℝ)^27 := by
    have hnat : (1159863631 : ℕ)^35*20000000000000^27 ≤ 3009180464017^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159863631 5000000000 3009180464017 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1823915179/2500000000 : ℝ), (544239493/2000000000 : ℝ), (1159863631/5000000000 : ℝ)] ![(13289883728179/20000000000000 : ℝ), (4626169755177/25000000000000 : ℝ), (3009180464017/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1823915179/2500000000 : ℝ)|^35 ≤ (13289883728179/20000000000000 : ℝ)^27
        have hw : |(1823915179/2500000000 : ℝ)|=(1823915179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(544239493/2000000000 : ℝ)|^35 ≤ (4626169755177/25000000000000 : ℝ)^27
        have hw : |(544239493/2000000000 : ℝ)|=(544239493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1159863631/5000000000 : ℝ)|^35 ≤ (3009180464017/20000000000000 : ℝ)^27
        have hw : |(1159863631/5000000000 : ℝ)|=(1159863631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309076_s1_s1_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1962592253/5000000000 : ℝ)*x 0 + (-5853841239/10000000000 : ℝ)*x 1 + (-730608101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1962592253/5000000000 : ℝ)^35 ≤ (7438105418981/25000000000000 : ℝ)^27 := by
    have hnat : (1962592253 : ℕ)^35*25000000000000^27 ≤ 7438105418981^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962592253 5000000000 7438105418981 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5853841239/10000000000 : ℝ)^35 ≤ (12487472945071/25000000000000 : ℝ)^27 := by
    have hnat : (5853841239 : ℕ)^35*25000000000000^27 ≤ 12487472945071^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5853841239 10000000000 12487472945071 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (730608101/2500000000 : ℝ)^35 ≤ (10148843268179/50000000000000 : ℝ)^27 := by
    have hnat : (730608101 : ℕ)^35*50000000000000^27 ≤ 10148843268179^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730608101 2500000000 10148843268179 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1962592253/5000000000 : ℝ), (-5853841239/10000000000 : ℝ), (-730608101/2500000000 : ℝ)] ![(7438105418981/25000000000000 : ℝ), (12487472945071/25000000000000 : ℝ), (10148843268179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1962592253/5000000000 : ℝ)|^35 ≤ (7438105418981/25000000000000 : ℝ)^27
        have hw : |(1962592253/5000000000 : ℝ)|=(1962592253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5853841239/10000000000 : ℝ)|^35 ≤ (12487472945071/25000000000000 : ℝ)^27
        have hw : |(-5853841239/10000000000 : ℝ)|=(5853841239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-730608101/2500000000 : ℝ)|^35 ≤ (10148843268179/50000000000000 : ℝ)^27
        have hw : |(-730608101/2500000000 : ℝ)|=(730608101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309076_s1_s1_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5911776141/10000000000 : ℝ)*x 0 + (667169/1250000000 : ℝ)*x 1 + (29021511/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5911776141/10000000000 : ℝ)^35 ≤ (50591652303067/100000000000000 : ℝ)^27 := by
    have hnat : (5911776141 : ℕ)^35*100000000000000^27 ≤ 50591652303067^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5911776141 10000000000 50591652303067 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (667169/1250000000 : ℝ)^35 ≤ (5723275009/100000000000000 : ℝ)^27 := by
    have hnat : (667169 : ℕ)^35*100000000000000^27 ≤ 5723275009^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667169 1250000000 5723275009 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29021511/50000000 : ℝ)^35 ≤ (49402624409701/100000000000000 : ℝ)^27 := by
    have hnat : (29021511 : ℕ)^35*100000000000000^27 ≤ 49402624409701^27*50000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29021511 50000000 49402624409701 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5911776141/10000000000 : ℝ), (667169/1250000000 : ℝ), (29021511/50000000 : ℝ)] ![(50591652303067/100000000000000 : ℝ), (5723275009/100000000000000 : ℝ), (49402624409701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5911776141/10000000000 : ℝ)|^35 ≤ (50591652303067/100000000000000 : ℝ)^27
        have hw : |(5911776141/10000000000 : ℝ)|=(5911776141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(667169/1250000000 : ℝ)|^35 ≤ (5723275009/100000000000000 : ℝ)^27
        have hw : |(667169/1250000000 : ℝ)|=(667169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(29021511/50000000 : ℝ)|^35 ≤ (49402624409701/100000000000000 : ℝ)^27
        have hw : |(29021511/50000000 : ℝ)|=(29021511/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309076_s1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((2129/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2129/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-42857/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-42857/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3649/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3649/4000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((321/500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(321/500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-64829/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-64829/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71393/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(71393/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (91323/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s1_pow0 : (2129/2500 : ℝ) ^ (69/16 : ℝ) ≤ (50019719567357034737/100000000000000000000 : ℝ) := by
    have hpowers : (2129/2500 : ℝ)^69 ≤ (50019719567357034737/100000000000000000000 : ℝ)^16 := by
      have hnat : (2129 : ℕ)^69*100000000000000000000^16 ≤ 50019719567357034737^16*2500^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2129 2500 50019719567357034737 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2129/2500 : ℝ)) (X := (50019719567357034737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (150019719567357034737/100000000000000000000 : ℝ) ≤ (10986161880552041/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (150019719567357034737/100000000000000000000 : ℝ)^16 ≤ (10986161880552041/10000000000000000 : ℝ)^69 := by
      have hnat : (150019719567357034737 : ℕ)^16*10000000000000000^69 ≤ 10986161880552041^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        150019719567357034737 100000000000000000000 10986161880552041 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10986161880552041/10000000000000000 : ℝ)) (X := (150019719567357034737/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (100019719567357034737/50000000000000000000 : ℝ) ≤ (11744212851903617/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (100019719567357034737/50000000000000000000 : ℝ)^16 ≤ (11744212851903617/10000000000000000 : ℝ)^69 := by
      have hnat : (100019719567357034737 : ℕ)^16*10000000000000000^69 ≤ 11744212851903617^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019719567357034737 50000000000000000000 11744212851903617 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11744212851903617/10000000000000000 : ℝ)) (X := (100019719567357034737/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(986161880552041/8516000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(94756371418947/1064500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (2129/2500 : ℝ)) (alpha := (986161880552041/8516000000000000 : ℝ)) (beta := (94756371418947/1064500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2129/2500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(986161880552041/8516000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(94756371418947/1064500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (42857/50000 : ℝ) ^ (69/16 : ℝ) ≤ (5143819573659177747/10000000000000000000 : ℝ) := by
    have hpowers : (42857/50000 : ℝ)^69 ≤ (5143819573659177747/10000000000000000000 : ℝ)^16 := by
      have hnat : (42857 : ℕ)^69*10000000000000000000^16 ≤ 5143819573659177747^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42857 50000 5143819573659177747 10000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42857/50000 : ℝ)) (X := (5143819573659177747/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (15143819573659177747/10000000000000000000 : ℝ) ≤ (11010162330819047/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (15143819573659177747/10000000000000000000 : ℝ)^16 ≤ (11010162330819047/10000000000000000 : ℝ)^69 := by
      have hnat : (15143819573659177747 : ℕ)^16*10000000000000000^69 ≤ 11010162330819047^69*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15143819573659177747 10000000000000000000 11010162330819047 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11010162330819047/10000000000000000 : ℝ)) (X := (15143819573659177747/10000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (10143819573659177747/5000000000000000000 : ℝ) ≤ (11782625917485723/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (10143819573659177747/5000000000000000000 : ℝ)^16 ≤ (11782625917485723/10000000000000000 : ℝ)^69 := by
      have hnat : (10143819573659177747 : ℕ)^16*10000000000000000^69 ≤ 11782625917485723^69*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10143819573659177747 5000000000000000000 11782625917485723 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11782625917485723/10000000000000000 : ℝ)) (X := (10143819573659177747/5000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(59421313577591/504200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(193115896666669/2142850000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (42857/50000 : ℝ)) (alpha := (59421313577591/504200000000000 : ℝ)) (beta := (193115896666669/2142850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (42857/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(59421313577591/504200000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(193115896666669/2142850000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (3649/4000 : ℝ) ^ (69/16 : ℝ) ≤ (67296282351726892581/100000000000000000000 : ℝ) := by
    have hpowers : (3649/4000 : ℝ)^69 ≤ (67296282351726892581/100000000000000000000 : ℝ)^16 := by
      have hnat : (3649 : ℕ)^69*100000000000000000000^16 ≤ 67296282351726892581^16*4000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3649 4000 67296282351726892581 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3649/4000 : ℝ)) (X := (67296282351726892581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (167296282351726892581/100000000000000000000 : ℝ) ≤ (1408422391146133/1250000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (167296282351726892581/100000000000000000000 : ℝ)^16 ≤ (1408422391146133/1250000000000000 : ℝ)^69 := by
      have hnat : (167296282351726892581 : ℕ)^16*1250000000000000^69 ≤ 1408422391146133^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        167296282351726892581 100000000000000000000 1408422391146133 1250000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1408422391146133/1250000000000000 : ℝ)) (X := (167296282351726892581/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (117296282351726892581/50000000000000000000 : ℝ) ≤ (12186246802579617/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (117296282351726892581/50000000000000000000 : ℝ)^16 ≤ (12186246802579617/10000000000000000 : ℝ)^69 := by
      have hnat : (117296282351726892581 : ℕ)^16*10000000000000000^69 ≤ 12186246802579617^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        117296282351726892581 50000000000000000000 12186246802579617 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12186246802579617/10000000000000000 : ℝ)) (X := (117296282351726892581/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(158422391146133/1140312500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(918867673410553/9122500000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (3649/4000 : ℝ)) (alpha := (158422391146133/1140312500000000 : ℝ)) (beta := (918867673410553/9122500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (3649/4000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(158422391146133/1140312500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(918867673410553/9122500000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-57696903/400000000 : ℝ)*X 0 0+(-6271489063/10000000000 : ℝ)*X 0 1+(2334385999/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309076_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((6395171679/10000000000 : ℝ)*X 1 0+(52245897/156250000 : ℝ)*X 1 1+(717106827/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309076_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1187096217/2500000000 : ℝ)*X 2 0+(-2298912107/5000000000 : ℝ)*X 2 1+(-217119171/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309076_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2630661/19531250 : ℝ)*X 0 0+(-919439549/1250000000 : ℝ)*X 0 1+(1737519499/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309076_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5510257479/10000000000 : ℝ)*X 1 0+(1021270017/2500000000 : ℝ)*X 1 1+(3162410029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309076_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1204827629/2500000000 : ℝ)*X 2 0+(-1318390207/2500000000 : ℝ)*X 2 1+(-2612494853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309076_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((643323631/2000000000 : ℝ)*X 0 0+(40148347/10000000000 : ℝ)*X 0 1+(8168840661/10000000000 : ℝ)*X 0 2+(643323631/2000000000 : ℝ)*X 1 0+(40148347/10000000000 : ℝ)*X 1 1+(8168840661/10000000000 : ℝ)*X 1 2+(643323631/2000000000 : ℝ)*X 2 0+(40148347/10000000000 : ℝ)*X 2 1+(8168840661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309076_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1065846341/10000000000 : ℝ)*X 0 0+(-2707056311/5000000000 : ℝ)*X 0 1+(580120641/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309076_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((7600017907/10000000000 : ℝ)*X 1 0+(1238896967/5000000000 : ℝ)*X 1 1+(2139335929/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309076_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((359450261/625000000 : ℝ)*X 2 0+(-2313865279/5000000000 : ℝ)*X 2 1+(-2236640137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309076_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1109570837/5000000000 : ℝ)*X 0 0+(-294047/10000000000 : ℝ)*X 0 1+(888520569/1000000000 : ℝ)*X 0 2+(1109570837/5000000000 : ℝ)*X 1 0+(-294047/10000000000 : ℝ)*X 1 1+(888520569/1000000000 : ℝ)*X 1 2+(1109570837/5000000000 : ℝ)*X 2 0+(-294047/10000000000 : ℝ)*X 2 1+(888520569/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309076_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-733526381/10000000000 : ℝ)*X 0 0+(-904071919/1250000000 : ℝ)*X 0 1+(1010668291/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309076_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1823915179/2500000000 : ℝ)*X 1 0+(544239493/2000000000 : ℝ)*X 1 1+(1159863631/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309076_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1962592253/5000000000 : ℝ)*X 2 0+(-5853841239/10000000000 : ℝ)*X 2 1+(-730608101/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309076_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((5911776141/10000000000 : ℝ)*X 0 0+(667169/1250000000 : ℝ)*X 0 1+(29021511/50000000 : ℝ)*X 0 2+(5911776141/10000000000 : ℝ)*X 1 0+(667169/1250000000 : ℝ)*X 1 1+(29021511/50000000 : ℝ)*X 1 2+(5911776141/10000000000 : ℝ)*X 2 0+(667169/1250000000 : ℝ)*X 2 1+(29021511/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309076_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((321/500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(321/500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1088410753921685160602241819/77687210000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24673145671/250000000000 : ℝ)*(base3) + (36803475573/62500000000 : ℝ)*(base7) + (3087799/1000000000000 : ℝ)*(base40) + (604870750031/1000000000000 : ℝ)*(base54) + (3017946775069/1000000000000 : ℝ)*(major_s1_0) + (3017946775069/1000000000000 : ℝ)*(major_s1_1) + (1206538012519/500000000000 : ℝ)*(major_s1_2) + (1192311/250000000000 : ℝ)*(sp_s1_0) + (4499143/250000000000 : ℝ)*(sp_s1_2) + (3782241321969/1000000000000 : ℝ)*(sp_s1_7) + (485117334237/125000000000 : ℝ)*(sp_s1_8) + (3177299452391/1000000000000 : ℝ)*(sp_s1_9) + (1780427993339/1000000000000 : ℝ)*(sp_s1_13) + (57892219/1000000000000 : ℝ)*(sp_s1_23) + (379027143377/200000000000 : ℝ)*(f.failure) + (3782246091213/1000000000000 : ℝ)*(f.sum) + (12135567865690569369/97740745625000000000000000000000 : ℝ)*base62 + (715265438458309/2280625000000000000000000000 : ℝ)*base64 + (703626905481/504200000000000000000000000 : ℝ)*base66 + (2505703477872091/4561250000000000000000000000 : ℝ)*base69 + (34502037821715041447/155374420000000000000000000000000 : ℝ)*base70 + (671429540125993/1064500000000000000000000000 : ℝ)*base73 + (13344501579897/66964062500000000000000000 : ℝ)*base75 + (7168864581151771/8516000000000000000000000000 : ℝ)*base76 + (1105410125574836661/5367209000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (22881/20000000000000000 : ℝ)*base86 + (22881/20000000000000000 : ℝ)*base88 + (22881/20000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-64829/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-64829/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13826034114510510541358559998787/1664720379485000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2215867/500000000000 : ℝ)*(base3) + (571128664953/1000000000000 : ℝ)*(base7) + (21939737901/500000000000 : ℝ)*(base33) + (271048295401/1000000000000 : ℝ)*(base40) + (15684393/1000000000000 : ℝ)*(base54) + (1448650943041/500000000000 : ℝ)*(major_s1_0) + (588236272377/200000000000 : ℝ)*(major_s1_1) + (2941165677491/1000000000000 : ℝ)*(major_s1_2) + (7280501/100000000000 : ℝ)*(sp_s1_13) + (3687714933833/1000000000000 : ℝ)*(sp_s1_14) + (910842158061/250000000000 : ℝ)*(sp_s1_15) + (1821909886819/500000000000 : ℝ)*(sp_s1_16) + (604491552877/250000000000 : ℝ)*(sp_s1_20) + (471257521/1000000000000 : ℝ)*(sp_s1_22) + (1846930467691/1000000000000 : ℝ)*(f.failure) + (3687714933833/1000000000000 : ℝ)*(f.sum) + (22445923518177341533/97740745625000000000000000000000 : ℝ)*base62 + (4813506059220477/9122500000000000000000000000 : ℝ)*base64 + (68789314275633/100840000000000000000000000 : ℝ)*base66 + (1867911103828769/2280625000000000000000000000 : ℝ)*base68 + (53804823524988564287/77687210000000000000000000000000 : ℝ)*base70 + (211625851095473/532250000000000000000000000 : ℝ)*base72 + (305380759380323/428570000000000000000000000 : ℝ)*base74 + (3379093574925319/4258000000000000000000000000 : ℝ)*base76 + (877008082164383443/5367209000000000000000000000000 : ℝ)*base79 + (11323/100000000000000000 : ℝ)*base86 + (111323/100000000000000000 : ℝ)*base88 + (11323/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71393/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(71393/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8446648963494549504117994915971/832360189742500000000000000000000000 : ℝ) := by norm_num
    linear_combination (222403224183/500000000000 : ℝ)*(base3) + (7475406341/10000000000 : ℝ)*(base7) + (1169437/250000000000 : ℝ)*(base22) + (138883161043/250000000000 : ℝ)*(base40) + (3551442401403/1000000000000 : ℝ)*(major_s1_0) + (3551442401403/1000000000000 : ℝ)*(major_s1_1) + (3551442401403/1000000000000 : ℝ)*(major_s1_2) + (7737011/1000000000000 : ℝ)*(sp_s1_0) + (12605337/1000000000000 : ℝ)*(sp_s1_1) + (6436041/100000000000 : ℝ)*(sp_s1_9) + (4417608863517/1000000000000 : ℝ)*(sp_s1_21) + (4862410443557/1000000000000 : ℝ)*(sp_s1_22) + (441754756237/100000000000 : ℝ)*(sp_s1_23) + (1266440658273/500000000000 : ℝ)*(sp_s1_27) + (2230147130811/1000000000000 : ℝ)*(f.failure) + (276101037533/62500000000 : ℝ)*(f.sum) + (18454726271629792703/195481491250000000000000000000000 : ℝ)*base62 + (1761172492897109/9122500000000000000000000000 : ℝ)*base65 + (76381426865547/504200000000000000000000000 : ℝ)*base66 + (1746579803605229/4561250000000000000000000000 : ℝ)*base68 + (22798388021599888377/155374420000000000000000000000000 : ℝ)*base70 + (161464421715859/1064500000000000000000000000 : ℝ)*base72 + (332175745193917/2142850000000000000000000000 : ℝ)*base74 + (1539388484762323/8516000000000000000000000000 : ℝ)*base77 + (238537777016673493/5367209000000000000000000000000 : ℝ)*base78 + (40683/100000000000000000 : ℝ)*base86 + (40683/100000000000000000 : ℝ)*base88 + (40683/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((2129/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2129/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-42857/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-42857/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3649/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3649/4000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((321/500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(321/500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-64829/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-64829/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71393/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(71393/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309076_s1 p hpa hpb X hX hprev0

#print axioms solution

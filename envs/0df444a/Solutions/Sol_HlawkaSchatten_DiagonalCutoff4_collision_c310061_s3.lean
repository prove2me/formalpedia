-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310061_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:28:04.855394+00:00
-- url     : https://prove2.me/submissions/b7269ec2-9209-462f-b923-1d540ed4ec6e

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
theorem collision_support_c310061_s3_s3_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121652581/10000000000 : ℝ)*x 0 + (2265589799/5000000000 : ℝ)*x 1 + (1178001257/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121652581/10000000000 : ℝ)^71 ≤ (13514428782411/100000000000000 : ℝ)^55 := by
    have hnat : (2121652581 : ℕ)^71*100000000000000^55 ≤ 13514428782411^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121652581 10000000000 13514428782411 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265589799/5000000000 : ℝ)^71 ≤ (35991505322893/100000000000000 : ℝ)^55 := by
    have hnat : (2265589799 : ℕ)^71*100000000000000^55 ≤ 35991505322893^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265589799 5000000000 35991505322893 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1178001257/2000000000 : ℝ)^71 ≤ (50494065888761/100000000000000 : ℝ)^55 := by
    have hnat : (1178001257 : ℕ)^71*100000000000000^55 ≤ 50494065888761^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178001257 2000000000 50494065888761 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121652581/10000000000 : ℝ), (2265589799/5000000000 : ℝ), (1178001257/2000000000 : ℝ)] ![(13514428782411/100000000000000 : ℝ), (35991505322893/100000000000000 : ℝ), (50494065888761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121652581/10000000000 : ℝ)|^71 ≤ (13514428782411/100000000000000 : ℝ)^55
        have hw : |(-2121652581/10000000000 : ℝ)|=(2121652581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2265589799/5000000000 : ℝ)|^71 ≤ (35991505322893/100000000000000 : ℝ)^55
        have hw : |(2265589799/5000000000 : ℝ)|=(2265589799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1178001257/2000000000 : ℝ)|^71 ≤ (50494065888761/100000000000000 : ℝ)^55
        have hw : |(1178001257/2000000000 : ℝ)|=(1178001257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s3_s3_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (299298673/625000000 : ℝ)*x 0 + (1572751647/2500000000 : ℝ)*x 1 + (-1184825103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (299298673/625000000 : ℝ)^71 ≤ (19327214116293/50000000000000 : ℝ)^55 := by
    have hnat : (299298673 : ℕ)^71*50000000000000^55 ≤ 19327214116293^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299298673 625000000 19327214116293 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1572751647/2500000000 : ℝ)^71 ≤ (27487548156221/50000000000000 : ℝ)^55 := by
    have hnat : (1572751647 : ℕ)^71*50000000000000^55 ≤ 27487548156221^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572751647 2500000000 27487548156221 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1184825103/10000000000 : ℝ)^71 ≤ (6370475446883/100000000000000 : ℝ)^55 := by
    have hnat : (1184825103 : ℕ)^71*100000000000000^55 ≤ 6370475446883^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184825103 10000000000 6370475446883 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(299298673/625000000 : ℝ), (1572751647/2500000000 : ℝ), (-1184825103/10000000000 : ℝ)] ![(19327214116293/50000000000000 : ℝ), (27487548156221/50000000000000 : ℝ), (6370475446883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(299298673/625000000 : ℝ)|^71 ≤ (19327214116293/50000000000000 : ℝ)^55
        have hw : |(299298673/625000000 : ℝ)|=(299298673/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1572751647/2500000000 : ℝ)|^71 ≤ (27487548156221/50000000000000 : ℝ)^55
        have hw : |(1572751647/2500000000 : ℝ)|=(1572751647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1184825103/10000000000 : ℝ)|^71 ≤ (6370475446883/100000000000000 : ℝ)^55
        have hw : |(-1184825103/10000000000 : ℝ)|=(1184825103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s3_s3_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1222004643/2000000000 : ℝ)*x 0 + (1477980731/5000000000 : ℝ)*x 1 + (888983039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1222004643/2000000000 : ℝ)^71 ≤ (26471026797703/50000000000000 : ℝ)^55 := by
    have hnat : (1222004643 : ℕ)^71*50000000000000^55 ≤ 26471026797703^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222004643 2000000000 26471026797703 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1477980731/5000000000 : ℝ)^71 ≤ (10367886440561/50000000000000 : ℝ)^55 := by
    have hnat : (1477980731 : ℕ)^71*50000000000000^55 ≤ 10367886440561^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1477980731 5000000000 10367886440561 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (888983039/2500000000 : ℝ)^71 ≤ (13161086754941/50000000000000 : ℝ)^55 := by
    have hnat : (888983039 : ℕ)^71*50000000000000^55 ≤ 13161086754941^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888983039 2500000000 13161086754941 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1222004643/2000000000 : ℝ), (1477980731/5000000000 : ℝ), (888983039/2500000000 : ℝ)] ![(26471026797703/50000000000000 : ℝ), (10367886440561/50000000000000 : ℝ), (13161086754941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1222004643/2000000000 : ℝ)|^71 ≤ (26471026797703/50000000000000 : ℝ)^55
        have hw : |(1222004643/2000000000 : ℝ)|=(1222004643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1477980731/5000000000 : ℝ)|^71 ≤ (10367886440561/50000000000000 : ℝ)^55
        have hw : |(1477980731/5000000000 : ℝ)|=(1477980731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(888983039/2500000000 : ℝ)|^71 ≤ (13161086754941/50000000000000 : ℝ)^55
        have hw : |(888983039/2500000000 : ℝ)|=(888983039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s3_s3_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2083025001/10000000000 : ℝ)*x 0 + (3781866413/10000000000 : ℝ)*x 1 + (3291960359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083025001/10000000000 : ℝ)^71 ≤ (6598823587213/50000000000000 : ℝ)^55 := by
    have hnat : (2083025001 : ℕ)^71*50000000000000^55 ≤ 6598823587213^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083025001 10000000000 6598823587213 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3781866413/10000000000 : ℝ)^71 ≤ (28500801546433/100000000000000 : ℝ)^55 := by
    have hnat : (3781866413 : ℕ)^71*100000000000000^55 ≤ 28500801546433^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3781866413 10000000000 28500801546433 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3291960359/5000000000 : ℝ)^71 ≤ (58301551258437/100000000000000 : ℝ)^55 := by
    have hnat : (3291960359 : ℕ)^71*100000000000000^55 ≤ 58301551258437^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3291960359 5000000000 58301551258437 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2083025001/10000000000 : ℝ), (3781866413/10000000000 : ℝ), (3291960359/5000000000 : ℝ)] ![(6598823587213/50000000000000 : ℝ), (28500801546433/100000000000000 : ℝ), (58301551258437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2083025001/10000000000 : ℝ)|^71 ≤ (6598823587213/50000000000000 : ℝ)^55
        have hw : |(-2083025001/10000000000 : ℝ)|=(2083025001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3781866413/10000000000 : ℝ)|^71 ≤ (28500801546433/100000000000000 : ℝ)^55
        have hw : |(3781866413/10000000000 : ℝ)|=(3781866413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3291960359/5000000000 : ℝ)|^71 ≤ (58301551258437/100000000000000 : ℝ)^55
        have hw : |(3291960359/5000000000 : ℝ)|=(3291960359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s3_s3_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2118888327/5000000000 : ℝ)*x 0 + (-158374253/1000000000 : ℝ)*x 1 + (1633308143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118888327/5000000000 : ℝ)^71 ≤ (16505897415561/50000000000000 : ℝ)^55 := by
    have hnat : (2118888327 : ℕ)^71*50000000000000^55 ≤ 16505897415561^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118888327 5000000000 16505897415561 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (158374253/1000000000 : ℝ)^71 ≤ (2316357333149/25000000000000 : ℝ)^55 := by
    have hnat : (158374253 : ℕ)^71*25000000000000^55 ≤ 2316357333149^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158374253 1000000000 2316357333149 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1633308143/2500000000 : ℝ)^71 ≤ (28861387912083/50000000000000 : ℝ)^55 := by
    have hnat : (1633308143 : ℕ)^71*50000000000000^55 ≤ 28861387912083^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633308143 2500000000 28861387912083 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118888327/5000000000 : ℝ), (-158374253/1000000000 : ℝ), (1633308143/2500000000 : ℝ)] ![(16505897415561/50000000000000 : ℝ), (2316357333149/25000000000000 : ℝ), (28861387912083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118888327/5000000000 : ℝ)|^71 ≤ (16505897415561/50000000000000 : ℝ)^55
        have hw : |(2118888327/5000000000 : ℝ)|=(2118888327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-158374253/1000000000 : ℝ)|^71 ≤ (2316357333149/25000000000000 : ℝ)^55
        have hw : |(-158374253/1000000000 : ℝ)|=(158374253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1633308143/2500000000 : ℝ)|^71 ≤ (28861387912083/50000000000000 : ℝ)^55
        have hw : |(1633308143/2500000000 : ℝ)|=(1633308143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s3_s3_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (432039149/1000000000 : ℝ)*x 0 + (7128717701/10000000000 : ℝ)*x 1 + (-79373779/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432039149/1000000000 : ℝ)^71 ≤ (33844917429523/100000000000000 : ℝ)^55 := by
    have hnat : (432039149 : ℕ)^71*100000000000000^55 ≤ 33844917429523^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432039149 1000000000 33844917429523 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7128717701/10000000000 : ℝ)^71 ≤ (64602764343611/100000000000000 : ℝ)^55 := by
    have hnat : (7128717701 : ℕ)^71*100000000000000^55 ≤ 64602764343611^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7128717701 10000000000 64602764343611 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79373779/2000000000 : ℝ)^71 ≤ (31046364241/2000000000000 : ℝ)^55 := by
    have hnat : (79373779 : ℕ)^71*2000000000000^55 ≤ 31046364241^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79373779 2000000000 31046364241 2000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432039149/1000000000 : ℝ), (7128717701/10000000000 : ℝ), (-79373779/2000000000 : ℝ)] ![(33844917429523/100000000000000 : ℝ), (64602764343611/100000000000000 : ℝ), (31046364241/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432039149/1000000000 : ℝ)|^71 ≤ (33844917429523/100000000000000 : ℝ)^55
        have hw : |(432039149/1000000000 : ℝ)|=(432039149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7128717701/10000000000 : ℝ)|^71 ≤ (64602764343611/100000000000000 : ℝ)^55
        have hw : |(7128717701/10000000000 : ℝ)|=(7128717701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-79373779/2000000000 : ℝ)|^71 ≤ (31046364241/2000000000000 : ℝ)^55
        have hw : |(-79373779/2000000000 : ℝ)|=(79373779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s3_s3_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (46669501/78125000 : ℝ)*x 0 + (4423035589/10000000000 : ℝ)*x 1 + (2143138259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46669501/78125000 : ℝ)^71 ≤ (5142214853221/10000000000000 : ℝ)^55 := by
    have hnat : (46669501 : ℕ)^71*10000000000000^55 ≤ 5142214853221^55*78125000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46669501 78125000 5142214853221 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4423035589/10000000000 : ℝ)^71 ≤ (1744324543849/5000000000000 : ℝ)^55 := by
    have hnat : (4423035589 : ℕ)^71*5000000000000^55 ≤ 1744324543849^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4423035589 10000000000 1744324543849 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2143138259/10000000000 : ℝ)^71 ≤ (13691360570979/100000000000000 : ℝ)^55 := by
    have hnat : (2143138259 : ℕ)^71*100000000000000^55 ≤ 13691360570979^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143138259 10000000000 13691360570979 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(46669501/78125000 : ℝ), (4423035589/10000000000 : ℝ), (2143138259/10000000000 : ℝ)] ![(5142214853221/10000000000000 : ℝ), (1744324543849/5000000000000 : ℝ), (13691360570979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(46669501/78125000 : ℝ)|^71 ≤ (5142214853221/10000000000000 : ℝ)^55
        have hw : |(46669501/78125000 : ℝ)|=(46669501/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4423035589/10000000000 : ℝ)|^71 ≤ (1744324543849/5000000000000 : ℝ)^55
        have hw : |(4423035589/10000000000 : ℝ)|=(4423035589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2143138259/10000000000 : ℝ)|^71 ≤ (13691360570979/100000000000000 : ℝ)^55
        have hw : |(2143138259/10000000000 : ℝ)|=(2143138259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s3_s3_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1084564691/10000000000 : ℝ)*x 0 + (227254637/500000000 : ℝ)*x 1 + (6573498761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084564691/10000000000 : ℝ)^71 ≤ (710415646263/12500000000000 : ℝ)^55 := by
    have hnat : (1084564691 : ℕ)^71*12500000000000^55 ≤ 710415646263^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084564691 10000000000 710415646263 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227254637/500000000 : ℝ)^71 ≤ (36134231421277/100000000000000 : ℝ)^55 := by
    have hnat : (227254637 : ℕ)^71*100000000000000^55 ≤ 36134231421277^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227254637 500000000 36134231421277 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6573498761/10000000000 : ℝ)^71 ≤ (29091221700761/50000000000000 : ℝ)^55 := by
    have hnat : (6573498761 : ℕ)^71*50000000000000^55 ≤ 29091221700761^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6573498761 10000000000 29091221700761 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1084564691/10000000000 : ℝ), (227254637/500000000 : ℝ), (6573498761/10000000000 : ℝ)] ![(710415646263/12500000000000 : ℝ), (36134231421277/100000000000000 : ℝ), (29091221700761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1084564691/10000000000 : ℝ)|^71 ≤ (710415646263/12500000000000 : ℝ)^55
        have hw : |(-1084564691/10000000000 : ℝ)|=(1084564691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(227254637/500000000 : ℝ)|^71 ≤ (36134231421277/100000000000000 : ℝ)^55
        have hw : |(227254637/500000000 : ℝ)|=(227254637/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6573498761/10000000000 : ℝ)|^71 ≤ (29091221700761/50000000000000 : ℝ)^55
        have hw : |(6573498761/10000000000 : ℝ)|=(6573498761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s3_s3_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4150701193/10000000000 : ℝ)*x 0 + (-1713555961/10000000000 : ℝ)*x 1 + (6522809771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4150701193/10000000000 : ℝ)^71 ≤ (16069395440911/50000000000000 : ℝ)^55 := by
    have hnat : (4150701193 : ℕ)^71*50000000000000^55 ≤ 16069395440911^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150701193 10000000000 16069395440911 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1713555961/10000000000 : ℝ)^71 ≤ (5128641532933/50000000000000 : ℝ)^55 := by
    have hnat : (1713555961 : ℕ)^71*50000000000000^55 ≤ 5128641532933^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713555961 10000000000 5128641532933 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6522809771/10000000000 : ℝ)^71 ≤ (57603926048587/100000000000000 : ℝ)^55 := by
    have hnat : (6522809771 : ℕ)^71*100000000000000^55 ≤ 57603926048587^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6522809771 10000000000 57603926048587 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4150701193/10000000000 : ℝ), (-1713555961/10000000000 : ℝ), (6522809771/10000000000 : ℝ)] ![(16069395440911/50000000000000 : ℝ), (5128641532933/50000000000000 : ℝ), (57603926048587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4150701193/10000000000 : ℝ)|^71 ≤ (16069395440911/50000000000000 : ℝ)^55
        have hw : |(4150701193/10000000000 : ℝ)|=(4150701193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1713555961/10000000000 : ℝ)|^71 ≤ (5128641532933/50000000000000 : ℝ)^55
        have hw : |(-1713555961/10000000000 : ℝ)|=(1713555961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6522809771/10000000000 : ℝ)|^71 ≤ (57603926048587/100000000000000 : ℝ)^55
        have hw : |(6522809771/10000000000 : ℝ)|=(6522809771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s3_s3_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2949323731/5000000000 : ℝ)*x 0 + (2822771199/5000000000 : ℝ)*x 1 + (-407291313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2949323731/5000000000 : ℝ)^71 ≤ (2023588642637/4000000000000 : ℝ)^55 := by
    have hnat : (2949323731 : ℕ)^71*4000000000000^55 ≤ 2023588642637^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2949323731 5000000000 2023588642637 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2822771199/5000000000 : ℝ)^71 ≤ (47805140226393/100000000000000 : ℝ)^55 := by
    have hnat : (2822771199 : ℕ)^71*100000000000000^55 ≤ 47805140226393^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2822771199 5000000000 47805140226393 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407291313/10000000000 : ℝ)^71 ≤ (321028739103/20000000000000 : ℝ)^55 := by
    have hnat : (407291313 : ℕ)^71*20000000000000^55 ≤ 321028739103^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407291313 10000000000 321028739103 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2949323731/5000000000 : ℝ), (2822771199/5000000000 : ℝ), (-407291313/10000000000 : ℝ)] ![(2023588642637/4000000000000 : ℝ), (47805140226393/100000000000000 : ℝ), (321028739103/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2949323731/5000000000 : ℝ)|^71 ≤ (2023588642637/4000000000000 : ℝ)^55
        have hw : |(2949323731/5000000000 : ℝ)|=(2949323731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2822771199/5000000000 : ℝ)|^71 ≤ (47805140226393/100000000000000 : ℝ)^55
        have hw : |(2822771199/5000000000 : ℝ)|=(2822771199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-407291313/10000000000 : ℝ)|^71 ≤ (321028739103/20000000000000 : ℝ)^55
        have hw : |(-407291313/10000000000 : ℝ)|=(407291313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s3_s3_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7464728589/10000000000 : ℝ)*x 0 + (649581047/2500000000 : ℝ)*x 1 + (2166441269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7464728589/10000000000 : ℝ)^71 ≤ (68560290059611/100000000000000 : ℝ)^55 := by
    have hnat : (7464728589 : ℕ)^71*100000000000000^55 ≤ 68560290059611^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7464728589 10000000000 68560290059611 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649581047/2500000000 : ℝ)^71 ≤ (17555867998693/100000000000000 : ℝ)^55 := by
    have hnat : (649581047 : ℕ)^71*100000000000000^55 ≤ 17555867998693^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649581047 2500000000 17555867998693 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2166441269/10000000000 : ℝ)^71 ≤ (6941920963761/50000000000000 : ℝ)^55 := by
    have hnat : (2166441269 : ℕ)^71*50000000000000^55 ≤ 6941920963761^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166441269 10000000000 6941920963761 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7464728589/10000000000 : ℝ), (649581047/2500000000 : ℝ), (2166441269/10000000000 : ℝ)] ![(68560290059611/100000000000000 : ℝ), (17555867998693/100000000000000 : ℝ), (6941920963761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7464728589/10000000000 : ℝ)|^71 ≤ (68560290059611/100000000000000 : ℝ)^55
        have hw : |(7464728589/10000000000 : ℝ)|=(7464728589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(649581047/2500000000 : ℝ)|^71 ≤ (17555867998693/100000000000000 : ℝ)^55
        have hw : |(649581047/2500000000 : ℝ)|=(649581047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2166441269/10000000000 : ℝ)|^71 ≤ (6941920963761/50000000000000 : ℝ)^55
        have hw : |(2166441269/10000000000 : ℝ)|=(2166441269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s3_s3_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-519411589/5000000000 : ℝ)*x 0 + (2681897643/5000000000 : ℝ)*x 1 + (1458525103/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519411589/5000000000 : ℝ)^71 ≤ (5375819160397/100000000000000 : ℝ)^55 := by
    have hnat : (519411589 : ℕ)^71*100000000000000^55 ≤ 5375819160397^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519411589 5000000000 5375819160397 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2681897643/5000000000 : ℝ)^71 ≤ (44747955366891/100000000000000 : ℝ)^55 := by
    have hnat : (2681897643 : ℕ)^71*100000000000000^55 ≤ 44747955366891^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681897643 5000000000 44747955366891 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1458525103/2500000000 : ℝ)^71 ≤ (24938112731043/50000000000000 : ℝ)^55 := by
    have hnat : (1458525103 : ℕ)^71*50000000000000^55 ≤ 24938112731043^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458525103 2500000000 24938112731043 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-519411589/5000000000 : ℝ), (2681897643/5000000000 : ℝ), (1458525103/2500000000 : ℝ)] ![(5375819160397/100000000000000 : ℝ), (44747955366891/100000000000000 : ℝ), (24938112731043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-519411589/5000000000 : ℝ)|^71 ≤ (5375819160397/100000000000000 : ℝ)^55
        have hw : |(-519411589/5000000000 : ℝ)|=(519411589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2681897643/5000000000 : ℝ)|^71 ≤ (44747955366891/100000000000000 : ℝ)^55
        have hw : |(2681897643/5000000000 : ℝ)|=(2681897643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1458525103/2500000000 : ℝ)|^71 ≤ (24938112731043/50000000000000 : ℝ)^55
        have hw : |(1458525103/2500000000 : ℝ)|=(1458525103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s3_s3_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (732721697/1250000000 : ℝ)*x 0 + (-553548139/5000000000 : ℝ)*x 1 + (529253091/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (732721697/1250000000 : ℝ)^71 ≤ (6272729942457/12500000000000 : ℝ)^55 := by
    have hnat : (732721697 : ℕ)^71*12500000000000^55 ≤ 6272729942457^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732721697 1250000000 6272729942457 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553548139/5000000000 : ℝ)^71 ≤ (729525109799/12500000000000 : ℝ)^55 := by
    have hnat : (553548139 : ℕ)^71*12500000000000^55 ≤ 729525109799^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553548139 5000000000 729525109799 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529253091/1000000000 : ℝ)^71 ≤ (21990979781739/50000000000000 : ℝ)^55 := by
    have hnat : (529253091 : ℕ)^71*50000000000000^55 ≤ 21990979781739^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529253091 1000000000 21990979781739 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(732721697/1250000000 : ℝ), (-553548139/5000000000 : ℝ), (529253091/1000000000 : ℝ)] ![(6272729942457/12500000000000 : ℝ), (729525109799/12500000000000 : ℝ), (21990979781739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(732721697/1250000000 : ℝ)|^71 ≤ (6272729942457/12500000000000 : ℝ)^55
        have hw : |(732721697/1250000000 : ℝ)|=(732721697/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553548139/5000000000 : ℝ)|^71 ≤ (729525109799/12500000000000 : ℝ)^55
        have hw : |(-553548139/5000000000 : ℝ)|=(553548139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529253091/1000000000 : ℝ)|^71 ≤ (21990979781739/50000000000000 : ℝ)^55
        have hw : |(529253091/1000000000 : ℝ)|=(529253091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s3_s3_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1024929877/2500000000 : ℝ)*x 0 + (7054579121/10000000000 : ℝ)*x 1 + (-925810307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1024929877/2500000000 : ℝ)^71 ≤ (3163011745741/10000000000000 : ℝ)^55 := by
    have hnat : (1024929877 : ℕ)^71*10000000000000^55 ≤ 3163011745741^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024929877 2500000000 3163011745741 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7054579121/10000000000 : ℝ)^71 ≤ (63736759108611/100000000000000 : ℝ)^55 := by
    have hnat : (7054579121 : ℕ)^71*100000000000000^55 ≤ 63736759108611^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7054579121 10000000000 63736759108611 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (925810307/10000000000 : ℝ)^71 ≤ (4633123419659/100000000000000 : ℝ)^55 := by
    have hnat : (925810307 : ℕ)^71*100000000000000^55 ≤ 4633123419659^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925810307 10000000000 4633123419659 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1024929877/2500000000 : ℝ), (7054579121/10000000000 : ℝ), (-925810307/10000000000 : ℝ)] ![(3163011745741/10000000000000 : ℝ), (63736759108611/100000000000000 : ℝ), (4633123419659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1024929877/2500000000 : ℝ)|^71 ≤ (3163011745741/10000000000000 : ℝ)^55
        have hw : |(1024929877/2500000000 : ℝ)|=(1024929877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7054579121/10000000000 : ℝ)|^71 ≤ (63736759108611/100000000000000 : ℝ)^55
        have hw : |(7054579121/10000000000 : ℝ)|=(7054579121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-925810307/10000000000 : ℝ)|^71 ≤ (4633123419659/100000000000000 : ℝ)^55
        have hw : |(-925810307/10000000000 : ℝ)|=(925810307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s3_s3_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (970428299/1250000000 : ℝ)*x 0 + (2117559589/10000000000 : ℝ)*x 1 + (557054297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (970428299/1250000000 : ℝ)^71 ≤ (36061101648309/50000000000000 : ℝ)^55 := by
    have hnat : (970428299 : ℕ)^71*50000000000000^55 ≤ 36061101648309^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970428299 1250000000 36061101648309 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117559589/10000000000 : ℝ)^71 ≤ (3370195606491/25000000000000 : ℝ)^55 := by
    have hnat : (2117559589 : ℕ)^71*25000000000000^55 ≤ 3370195606491^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117559589 10000000000 3370195606491 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (557054297/2500000000 : ℝ)^71 ≤ (14397014261601/100000000000000 : ℝ)^55 := by
    have hnat : (557054297 : ℕ)^71*100000000000000^55 ≤ 14397014261601^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557054297 2500000000 14397014261601 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(970428299/1250000000 : ℝ), (2117559589/10000000000 : ℝ), (557054297/2500000000 : ℝ)] ![(36061101648309/50000000000000 : ℝ), (3370195606491/25000000000000 : ℝ), (14397014261601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(970428299/1250000000 : ℝ)|^71 ≤ (36061101648309/50000000000000 : ℝ)^55
        have hw : |(970428299/1250000000 : ℝ)|=(970428299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117559589/10000000000 : ℝ)|^71 ≤ (3370195606491/25000000000000 : ℝ)^55
        have hw : |(2117559589/10000000000 : ℝ)|=(2117559589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(557054297/2500000000 : ℝ)|^71 ≤ (14397014261601/100000000000000 : ℝ)^55
        have hw : |(557054297/2500000000 : ℝ)|=(557054297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310061_s3 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((59399/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(59399/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31631/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31631/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57919/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57919/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1453/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1453/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21111/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21111/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19293/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19293/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (59399/100000 : ℝ) ^ (35/8 : ℝ) ≤ (1279952115100914457/12500000000000000000 : ℝ) := by
    have hpowers : (59399/100000 : ℝ)^35 ≤ (1279952115100914457/12500000000000000000 : ℝ)^8 := by
      have hnat : (59399 : ℕ)^35*12500000000000000000^8 ≤ 1279952115100914457^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59399 100000 1279952115100914457 12500000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59399/100000 : ℝ)) (X := (1279952115100914457/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner0a : (13779952115100914457/12500000000000000000 : ℝ) ≤ (5112663289693399/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (13779952115100914457/12500000000000000000 : ℝ)^8 ≤ (5112663289693399/5000000000000000 : ℝ)^35 := by
      have hnat : (13779952115100914457 : ℕ)^8*5000000000000000^35 ≤ 5112663289693399^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13779952115100914457 12500000000000000000 5112663289693399 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5112663289693399/5000000000000000 : ℝ)) (X := (13779952115100914457/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner0b : (7529952115100914457/6250000000000000000 : ℝ) ≤ (5217521181138111/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (7529952115100914457/6250000000000000000 : ℝ)^8 ≤ (5217521181138111/5000000000000000 : ℝ)^35 := by
      have hnat : (7529952115100914457 : ℕ)^8*5000000000000000^35 ≤ 5217521181138111^35*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7529952115100914457 6250000000000000000 5217521181138111 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5217521181138111/5000000000000000 : ℝ)) (X := (7529952115100914457/6250000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(112663289693399/2969950000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(13107236430589/371243750000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (59399/100000 : ℝ)) (alpha := (112663289693399/2969950000000000 : ℝ)) (beta := (13107236430589/371243750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (59399/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(112663289693399/2969950000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(13107236430589/371243750000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (31631/50000 : ℝ) ^ (35/8 : ℝ) ≤ (13489637071954083901/100000000000000000000 : ℝ) := by
    have hpowers : (31631/50000 : ℝ)^35 ≤ (13489637071954083901/100000000000000000000 : ℝ)^8 := by
      have hnat : (31631 : ℕ)^35*100000000000000000000^8 ≤ 13489637071954083901^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31631 50000 13489637071954083901 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31631/50000 : ℝ)) (X := (13489637071954083901/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner1a : (113489637071954083901/100000000000000000000 : ℝ) ≤ (10293460890630413/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (113489637071954083901/100000000000000000000 : ℝ)^8 ≤ (10293460890630413/10000000000000000 : ℝ)^35 := by
      have hnat : (113489637071954083901 : ℕ)^8*10000000000000000^35 ≤ 10293460890630413^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113489637071954083901 100000000000000000000 10293460890630413 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10293460890630413/10000000000000000 : ℝ)) (X := (113489637071954083901/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner1b : (63489637071954083901/50000000000000000000 : ℝ) ≤ (10561129391003197/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (63489637071954083901/50000000000000000000 : ℝ)^8 ≤ (10561129391003197/10000000000000000 : ℝ)^35 := by
      have hnat : (63489637071954083901 : ℕ)^8*10000000000000000^35 ≤ 10561129391003197^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63489637071954083901 50000000000000000000 10561129391003197 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10561129391003197/10000000000000000 : ℝ)) (X := (63489637071954083901/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(293460890630413/6326200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(16729281273299/395387500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (31631/50000 : ℝ)) (alpha := (293460890630413/6326200000000000 : ℝ)) (beta := (16729281273299/395387500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (31631/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(293460890630413/6326200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(16729281273299/395387500000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (57919/100000 : ℝ) ^ (35/8 : ℝ) ≤ (9169425269808056677/100000000000000000000 : ℝ) := by
    have hpowers : (57919/100000 : ℝ)^35 ≤ (9169425269808056677/100000000000000000000 : ℝ)^8 := by
      have hnat : (57919 : ℕ)^35*100000000000000000000^8 ≤ 9169425269808056677^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57919 100000 9169425269808056677 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (57919/100000 : ℝ)) (X := (9169425269808056677/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner2a : (109169425269808056677/100000000000000000000 : ℝ) ≤ (318829741575131/312500000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (109169425269808056677/100000000000000000000 : ℝ)^8 ≤ (318829741575131/312500000000000 : ℝ)^35 := by
      have hnat : (109169425269808056677 : ℕ)^8*312500000000000^35 ≤ 318829741575131^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109169425269808056677 100000000000000000000 318829741575131 312500000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (318829741575131/312500000000000 : ℝ)) (X := (109169425269808056677/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner2b : (59169425269808056677/50000000000000000000 : ℝ) ≤ (10392375300788753/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (59169425269808056677/50000000000000000000 : ℝ)^8 ≤ (10392375300788753/10000000000000000 : ℝ)^35 := by
      have hnat : (59169425269808056677 : ℕ)^8*10000000000000000^35 ≤ 10392375300788753^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59169425269808056677 50000000000000000000 10392375300788753 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10392375300788753/10000000000000000 : ℝ)) (X := (59169425269808056677/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(6329741575131/180996875000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(189823570384561/5791900000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (57919/100000 : ℝ)) (alpha := (6329741575131/180996875000000 : ℝ)) (beta := (189823570384561/5791900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (57919/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(6329741575131/180996875000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(189823570384561/5791900000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-2121652581/10000000000 : ℝ)*X 0 0+(2265589799/5000000000 : ℝ)*X 0 1+(1178001257/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((299298673/625000000 : ℝ)*X 2 0+(1572751647/2500000000 : ℝ)*X 2 1+(-1184825103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((1222004643/2000000000 : ℝ)*X 0 0+(1477980731/5000000000 : ℝ)*X 0 1+(888983039/2500000000 : ℝ)*X 0 2+(1222004643/2000000000 : ℝ)*X 1 0+(1477980731/5000000000 : ℝ)*X 1 1+(888983039/2500000000 : ℝ)*X 1 2+(1222004643/2000000000 : ℝ)*X 2 0+(1477980731/5000000000 : ℝ)*X 2 1+(888983039/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-2083025001/10000000000 : ℝ)*X 0 0+(3781866413/10000000000 : ℝ)*X 0 1+(3291960359/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((2118888327/5000000000 : ℝ)*X 1 0+(-158374253/1000000000 : ℝ)*X 1 1+(1633308143/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((432039149/1000000000 : ℝ)*X 2 0+(7128717701/10000000000 : ℝ)*X 2 1+(-79373779/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((46669501/78125000 : ℝ)*X 0 0+(4423035589/10000000000 : ℝ)*X 0 1+(2143138259/10000000000 : ℝ)*X 0 2+(46669501/78125000 : ℝ)*X 1 0+(4423035589/10000000000 : ℝ)*X 1 1+(2143138259/10000000000 : ℝ)*X 1 2+(46669501/78125000 : ℝ)*X 2 0+(4423035589/10000000000 : ℝ)*X 2 1+(2143138259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1084564691/10000000000 : ℝ)*X 0 0+(227254637/500000000 : ℝ)*X 0 1+(6573498761/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((4150701193/10000000000 : ℝ)*X 1 0+(-1713555961/10000000000 : ℝ)*X 1 1+(6522809771/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((2949323731/5000000000 : ℝ)*X 2 0+(2822771199/5000000000 : ℝ)*X 2 1+(-407291313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((7464728589/10000000000 : ℝ)*X 0 0+(649581047/2500000000 : ℝ)*X 0 1+(2166441269/10000000000 : ℝ)*X 0 2+(7464728589/10000000000 : ℝ)*X 1 0+(649581047/2500000000 : ℝ)*X 1 1+(2166441269/10000000000 : ℝ)*X 1 2+(7464728589/10000000000 : ℝ)*X 2 0+(649581047/2500000000 : ℝ)*X 2 1+(2166441269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-519411589/5000000000 : ℝ)*X 0 0+(2681897643/5000000000 : ℝ)*X 0 1+(1458525103/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((732721697/1250000000 : ℝ)*X 1 0+(-553548139/5000000000 : ℝ)*X 1 1+(529253091/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((1024929877/2500000000 : ℝ)*X 2 0+(7054579121/10000000000 : ℝ)*X 2 1+(-925810307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((970428299/1250000000 : ℝ)*X 0 0+(2117559589/10000000000 : ℝ)*X 0 1+(557054297/2500000000 : ℝ)*X 0 2+(970428299/1250000000 : ℝ)*X 1 0+(2117559589/10000000000 : ℝ)*X 1 1+(557054297/2500000000 : ℝ)*X 1 2+(970428299/1250000000 : ℝ)*X 2 0+(2117559589/10000000000 : ℝ)*X 2 1+(557054297/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((1453/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1453/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (22085705227220825602242723200487/2176421995414220000000000000000000000 : ℝ) := by norm_num
    linear_combination (668951/200000000000 : ℝ)*(base23) + (123757/125000000000 : ℝ)*(base50) + (97032064711/125000000000 : ℝ)*(base59) + (4533563244201/1000000000000 : ℝ)*(major_s3_0) + (4533563244201/1000000000000 : ℝ)*(major_s3_1) + (4533563244201/1000000000000 : ℝ)*(major_s3_2) + (6884127/500000000000 : ℝ)*(sp_s3_0) + (534199/31250000000 : ℝ)*(sp_s3_6) + (6265033077041/1000000000000 : ℝ)*(sp_s3_7) + (6264658230203/1000000000000 : ℝ)*(sp_s3_8) + (3132486993007/500000000000 : ℝ)*(sp_s3_9) + (2802059166163/1000000000000 : ℝ)*(sp_s3_13) + (97153773/250000000000 : ℝ)*(sp_s3_15) + (2780581/40000000000 : ℝ)*(sp_s3_23) + (2802076260531/1000000000000 : ℝ)*(f.failure) + (1253009369059/200000000000 : ℝ)*(f.sum) + (13807523764438518231/366407177800000000000000000000000 : ℝ)*base63 + (3702469156726119/5791900000000000000000000000 : ℝ)*base65 + (359568963367181/1581550000000000000000000000 : ℝ)*base67 + (404014137721803/1447975000000000000000000000 : ℝ)*base69 + (87134334062614048113/344033068100000000000000000000000 : ℝ)*base71 + (1039579388552477/2969950000000000000000000000 : ℝ)*base73 + (4891632159059733/6326200000000000000000000000 : ℝ)*base75 + (2917959899652009/2969950000000000000000000000 : ℝ)*base77 + (3426862243897774681/23485622112500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (7917/100000000000000000 : ℝ)*base86 + (7917/100000000000000000 : ℝ)*base88 + (7917/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21111/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21111/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (33897414150299799404901/2895950000000000000000000000 : ℝ) := by norm_num
    linear_combination (154627/200000000000 : ℝ)*(base39) + (911089/1000000000000 : ℝ)*(base49) + (176779993429/500000000000 : ℝ)*(base59) + (271578658307/62500000000 : ℝ)*(major_s3_0) + (271578658307/62500000000 : ℝ)*(major_s3_1) + (271578658307/62500000000 : ℝ)*(major_s3_2) + (23610941/1000000000000 : ℝ)*(sp_s3_2) + (4558353/250000000000 : ℝ)*(sp_s3_6) + (53665353/1000000000000 : ℝ)*(sp_s3_7) + (240190777201/40000000000 : ℝ)*(sp_s3_14) + (3002411547689/500000000000 : ℝ)*(sp_s3_15) + (3002399742219/500000000000 : ℝ)*(sp_s3_16) + (2685536105597/1000000000000 : ℝ)*(sp_s3_20) + (2120777/15625000000 : ℝ)*(sp_s3_27) + (2685690068737/1000000000000 : ℝ)*(f.failure) + (3002411547689/500000000000 : ℝ)*(f.sum) + (25167696259027807383/91601794450000000000000000000000 : ℝ)*base63 + (358648631876889/2895950000000000000000000000 : ℝ)*base65 + (13256956676859/49423437500000000000000000 : ℝ)*base66 + (217879459071533/2895950000000000000000000000 : ℝ)*base68 + (34757023215129521159/86008267025000000000000000000000 : ℝ)*base71 + (669006310326821/2969950000000000000000000000 : ℝ)*base72 + (961013636198951/1581550000000000000000000000 : ℝ)*base74 + (604954362520023/742487500000000000000000000 : ℝ)*base76 + (558015307095052059/11742811056250000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (34559/100000000000000000 : ℝ)*base86 + (34559/100000000000000000 : ℝ)*base88 + (34559/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19293/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19293/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (21335227708107271055162583120963/1360263747133887500000000000000000000 : ℝ) := by norm_num
    linear_combination (9513959/1000000000000 : ℝ)*(base15) + (33264364949/125000000000 : ℝ)*(base40) + (373083843539/1000000000000 : ℝ)*(base59) + (1961420045649/500000000000 : ℝ)*(major_s3_0) + (1961420045649/500000000000 : ℝ)*(major_s3_1) + (1961420045649/500000000000 : ℝ)*(major_s3_2) + (1196657/250000000000 : ℝ)*(sp_s3_0) + (137583927/1000000000000 : ℝ)*(sp_s3_2) + (2276241/25000000000 : ℝ)*(sp_s3_9) + (57717779/200000000000 : ℝ)*(sp_s3_20) + (2710532916511/500000000000 : ℝ)*(sp_s3_21) + (5421061105691/1000000000000 : ℝ)*(sp_s3_22) + (5420841986083/1000000000000 : ℝ)*(sp_s3_23) + (30303946823/12500000000 : ℝ)*(sp_s3_27) + (484920866947/200000000000 : ℝ)*(f.failure) + (108421412393/20000000000 : ℝ)*(f.sum) + (536305580447195909/183203588900000000000000000000000 : ℝ)*base63 + (86512756813409/2895950000000000000000000000 : ℝ)*base64 + (231646264009963/1581550000000000000000000000 : ℝ)*base67 + (131638388198263/2895950000000000000000000000 : ℝ)*base69 + (59069654648179243983/172016534050000000000000000000000 : ℝ)*base70 + (1315966022343601/2969950000000000000000000000 : ℝ)*base73 + (427765156111187/3163100000000000000000000000 : ℝ)*base75 + (195124766852203/2969950000000000000000000000 : ℝ)*base76 + (20534105451472494363/93942488450000000000000000000000 : ℝ)*base79 + (4029/20000000000000000 : ℝ)*base86 + (4029/20000000000000000 : ℝ)*base88 + (4029/20000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((59399/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(59399/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31631/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31631/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57919/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57919/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1453/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1453/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21111/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21111/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19293/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19293/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310061_s3 p hpa hpb X hX hprev2

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302052_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:17:53.777308+00:00
-- url     : https://prove2.me/submissions/06b0379f-2225-479c-9032-d7e1df2ef15d

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
theorem collision_support_c302052_s3_s3_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2515705299/10000000000 : ℝ)*x 0 + (1820937819/5000000000 : ℝ)*x 1 + (-1633104911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2515705299/10000000000 : ℝ)^67 ≤ (1019791699469/6250000000000 : ℝ)^51 := by
    have hnat : (2515705299 : ℕ)^67*6250000000000^51 ≤ 1019791699469^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2515705299 10000000000 1019791699469 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1820937819/5000000000 : ℝ)^67 ≤ (13263911681007/50000000000000 : ℝ)^51 := by
    have hnat : (1820937819 : ℕ)^67*50000000000000^51 ≤ 13263911681007^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820937819 5000000000 13263911681007 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1633104911/2500000000 : ℝ)^67 ≤ (1428887735813/2500000000000 : ℝ)^51 := by
    have hnat : (1633104911 : ℕ)^67*2500000000000^51 ≤ 1428887735813^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633104911 2500000000 1428887735813 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2515705299/10000000000 : ℝ), (1820937819/5000000000 : ℝ), (-1633104911/2500000000 : ℝ)] ![(1019791699469/6250000000000 : ℝ), (13263911681007/50000000000000 : ℝ), (1428887735813/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2515705299/10000000000 : ℝ)|^67 ≤ (1019791699469/6250000000000 : ℝ)^51
        have hw : |(-2515705299/10000000000 : ℝ)|=(2515705299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1820937819/5000000000 : ℝ)|^67 ≤ (13263911681007/50000000000000 : ℝ)^51
        have hw : |(1820937819/5000000000 : ℝ)|=(1820937819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1633104911/2500000000 : ℝ)|^67 ≤ (1428887735813/2500000000000 : ℝ)^51
        have hw : |(-1633104911/2500000000 : ℝ)|=(1633104911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s3_s3_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (577728207/1250000000 : ℝ)*x 0 + (-177734571/500000000 : ℝ)*x 1 + (-4790094033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (577728207/1250000000 : ℝ)^67 ≤ (36279143761071/100000000000000 : ℝ)^51 := by
    have hnat : (577728207 : ℕ)^67*100000000000000^51 ≤ 36279143761071^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      577728207 1250000000 36279143761071 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177734571/500000000 : ℝ)^67 ≤ (200755311291/781250000000 : ℝ)^51 := by
    have hnat : (177734571 : ℕ)^67*781250000000^51 ≤ 200755311291^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177734571 500000000 200755311291 781250000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4790094033/10000000000 : ℝ)^67 ≤ (19012088195921/50000000000000 : ℝ)^51 := by
    have hnat : (4790094033 : ℕ)^67*50000000000000^51 ≤ 19012088195921^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4790094033 10000000000 19012088195921 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(577728207/1250000000 : ℝ), (-177734571/500000000 : ℝ), (-4790094033/10000000000 : ℝ)] ![(36279143761071/100000000000000 : ℝ), (200755311291/781250000000 : ℝ), (19012088195921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(577728207/1250000000 : ℝ)|^67 ≤ (36279143761071/100000000000000 : ℝ)^51
        have hw : |(577728207/1250000000 : ℝ)|=(577728207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-177734571/500000000 : ℝ)|^67 ≤ (200755311291/781250000000 : ℝ)^51
        have hw : |(-177734571/500000000 : ℝ)|=(177734571/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4790094033/10000000000 : ℝ)|^67 ≤ (19012088195921/50000000000000 : ℝ)^51
        have hw : |(-4790094033/10000000000 : ℝ)|=(4790094033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s3_s3_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (486206669/1000000000 : ℝ)*x 0 + (5548365829/10000000000 : ℝ)*x 1 + (592961487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (486206669/1000000000 : ℝ)^67 ≤ (3877650372509/10000000000000 : ℝ)^51 := by
    have hnat : (486206669 : ℕ)^67*10000000000000^51 ≤ 3877650372509^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486206669 1000000000 3877650372509 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5548365829/10000000000 : ℝ)^67 ≤ (46121471535533/100000000000000 : ℝ)^51 := by
    have hnat : (5548365829 : ℕ)^67*100000000000000^51 ≤ 46121471535533^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5548365829 10000000000 46121471535533 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (592961487/2500000000 : ℝ)^67 ≤ (471938272781/3125000000000 : ℝ)^51 := by
    have hnat : (592961487 : ℕ)^67*3125000000000^51 ≤ 471938272781^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592961487 2500000000 471938272781 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(486206669/1000000000 : ℝ), (5548365829/10000000000 : ℝ), (592961487/2500000000 : ℝ)] ![(3877650372509/10000000000000 : ℝ), (46121471535533/100000000000000 : ℝ), (471938272781/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(486206669/1000000000 : ℝ)|^67 ≤ (3877650372509/10000000000000 : ℝ)^51
        have hw : |(486206669/1000000000 : ℝ)|=(486206669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5548365829/10000000000 : ℝ)|^67 ≤ (46121471535533/100000000000000 : ℝ)^51
        have hw : |(5548365829/10000000000 : ℝ)|=(5548365829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(592961487/2500000000 : ℝ)|^67 ≤ (471938272781/3125000000000 : ℝ)^51
        have hw : |(592961487/2500000000 : ℝ)|=(592961487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s3_s3_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5884366667/10000000000 : ℝ)*x 0 + (879351699/2000000000 : ℝ)*x 1 + (-2501847493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5884366667/10000000000 : ℝ)^67 ≤ (3114072202779/6250000000000 : ℝ)^51 := by
    have hnat : (5884366667 : ℕ)^67*6250000000000^51 ≤ 3114072202779^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5884366667 10000000000 3114072202779 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (879351699/2000000000 : ℝ)^67 ≤ (3397615387959/10000000000000 : ℝ)^51 := by
    have hnat : (879351699 : ℕ)^67*10000000000000^51 ≤ 3397615387959^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879351699 2000000000 3397615387959 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2501847493/10000000000 : ℝ)^67 ≤ (8099345429349/50000000000000 : ℝ)^51 := by
    have hnat : (2501847493 : ℕ)^67*50000000000000^51 ≤ 8099345429349^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2501847493 10000000000 8099345429349 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5884366667/10000000000 : ℝ), (879351699/2000000000 : ℝ), (-2501847493/10000000000 : ℝ)] ![(3114072202779/6250000000000 : ℝ), (3397615387959/10000000000000 : ℝ), (8099345429349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5884366667/10000000000 : ℝ)|^67 ≤ (3114072202779/6250000000000 : ℝ)^51
        have hw : |(5884366667/10000000000 : ℝ)|=(5884366667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(879351699/2000000000 : ℝ)|^67 ≤ (3397615387959/10000000000000 : ℝ)^51
        have hw : |(879351699/2000000000 : ℝ)|=(879351699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2501847493/10000000000 : ℝ)|^67 ≤ (8099345429349/50000000000000 : ℝ)^51
        have hw : |(-2501847493/10000000000 : ℝ)|=(2501847493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s3_s3_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1197117477/5000000000 : ℝ)*x 0 + (304511739/1000000000 : ℝ)*x 1 + (-3548886023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1197117477/5000000000 : ℝ)^67 ≤ (3057916005969/20000000000000 : ℝ)^51 := by
    have hnat : (1197117477 : ℕ)^67*20000000000000^51 ≤ 3057916005969^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197117477 5000000000 3057916005969 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (304511739/1000000000 : ℝ)^67 ≤ (4193990662831/20000000000000 : ℝ)^51 := by
    have hnat : (304511739 : ℕ)^67*20000000000000^51 ≤ 4193990662831^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304511739 1000000000 4193990662831 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3548886023/5000000000 : ℝ)^67 ≤ (796755833067/1250000000000 : ℝ)^51 := by
    have hnat : (3548886023 : ℕ)^67*1250000000000^51 ≤ 796755833067^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3548886023 5000000000 796755833067 1250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1197117477/5000000000 : ℝ), (304511739/1000000000 : ℝ), (-3548886023/5000000000 : ℝ)] ![(3057916005969/20000000000000 : ℝ), (4193990662831/20000000000000 : ℝ), (796755833067/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1197117477/5000000000 : ℝ)|^67 ≤ (3057916005969/20000000000000 : ℝ)^51
        have hw : |(-1197117477/5000000000 : ℝ)|=(1197117477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(304511739/1000000000 : ℝ)|^67 ≤ (4193990662831/20000000000000 : ℝ)^51
        have hw : |(304511739/1000000000 : ℝ)|=(304511739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3548886023/5000000000 : ℝ)|^67 ≤ (796755833067/1250000000000 : ℝ)^51
        have hw : |(-3548886023/5000000000 : ℝ)|=(3548886023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s3_s3_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1081548737/2500000000 : ℝ)*x 0 + (-351328047/1250000000 : ℝ)*x 1 + (-713400109/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081548737/2500000000 : ℝ)^67 ≤ (8315402924487/25000000000000 : ℝ)^51 := by
    have hnat : (1081548737 : ℕ)^67*25000000000000^51 ≤ 8315402924487^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081548737 2500000000 8315402924487 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (351328047/1250000000 : ℝ)^67 ≤ (18874619243383/100000000000000 : ℝ)^51 := by
    have hnat : (351328047 : ℕ)^67*100000000000000^51 ≤ 18874619243383^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351328047 1250000000 18874619243383 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (713400109/1250000000 : ℝ)^67 ≤ (4786376905011/10000000000000 : ℝ)^51 := by
    have hnat : (713400109 : ℕ)^67*10000000000000^51 ≤ 4786376905011^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713400109 1250000000 4786376905011 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081548737/2500000000 : ℝ), (-351328047/1250000000 : ℝ), (-713400109/1250000000 : ℝ)] ![(8315402924487/25000000000000 : ℝ), (18874619243383/100000000000000 : ℝ), (4786376905011/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081548737/2500000000 : ℝ)|^67 ≤ (8315402924487/25000000000000 : ℝ)^51
        have hw : |(1081548737/2500000000 : ℝ)|=(1081548737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-351328047/1250000000 : ℝ)|^67 ≤ (18874619243383/100000000000000 : ℝ)^51
        have hw : |(-351328047/1250000000 : ℝ)|=(351328047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-713400109/1250000000 : ℝ)|^67 ≤ (4786376905011/10000000000000 : ℝ)^51
        have hw : |(-713400109/1250000000 : ℝ)|=(713400109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s3_s3_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4567954033/10000000000 : ℝ)*x 0 + (1608023279/2500000000 : ℝ)*x 1 + (37494061/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4567954033/10000000000 : ℝ)^67 ≤ (17862315693219/50000000000000 : ℝ)^51 := by
    have hnat : (4567954033 : ℕ)^67*50000000000000^51 ≤ 17862315693219^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4567954033 10000000000 17862315693219 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1608023279/2500000000 : ℝ)^67 ≤ (28002549002327/50000000000000 : ℝ)^51 := by
    have hnat : (1608023279 : ℕ)^67*50000000000000^51 ≤ 28002549002327^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1608023279 2500000000 28002549002327 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37494061/250000000 : ℝ)^67 ≤ (8270270592917/100000000000000 : ℝ)^51 := by
    have hnat : (37494061 : ℕ)^67*100000000000000^51 ≤ 8270270592917^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37494061 250000000 8270270592917 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4567954033/10000000000 : ℝ), (1608023279/2500000000 : ℝ), (37494061/250000000 : ℝ)] ![(17862315693219/50000000000000 : ℝ), (28002549002327/50000000000000 : ℝ), (8270270592917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4567954033/10000000000 : ℝ)|^67 ≤ (17862315693219/50000000000000 : ℝ)^51
        have hw : |(4567954033/10000000000 : ℝ)|=(4567954033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1608023279/2500000000 : ℝ)|^67 ≤ (28002549002327/50000000000000 : ℝ)^51
        have hw : |(1608023279/2500000000 : ℝ)|=(1608023279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(37494061/250000000 : ℝ)|^67 ≤ (8270270592917/100000000000000 : ℝ)^51
        have hw : |(37494061/250000000 : ℝ)|=(37494061/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s3_s3_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1403015489/2500000000 : ℝ)*x 0 + (5462308327/10000000000 : ℝ)*x 1 + (-146198871/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1403015489/2500000000 : ℝ)^67 ≤ (46818314721363/100000000000000 : ℝ)^51 := by
    have hnat : (1403015489 : ℕ)^67*100000000000000^51 ≤ 46818314721363^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403015489 2500000000 46818314721363 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462308327/10000000000 : ℝ)^67 ≤ (45183974902081/100000000000000 : ℝ)^51 := by
    have hnat : (5462308327 : ℕ)^67*100000000000000^51 ≤ 45183974902081^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462308327 10000000000 45183974902081 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146198871/1000000000 : ℝ)^67 ≤ (7997710357849/100000000000000 : ℝ)^51 := by
    have hnat : (146198871 : ℕ)^67*100000000000000^51 ≤ 7997710357849^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146198871 1000000000 7997710357849 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1403015489/2500000000 : ℝ), (5462308327/10000000000 : ℝ), (-146198871/1000000000 : ℝ)] ![(46818314721363/100000000000000 : ℝ), (45183974902081/100000000000000 : ℝ), (7997710357849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1403015489/2500000000 : ℝ)|^67 ≤ (46818314721363/100000000000000 : ℝ)^51
        have hw : |(1403015489/2500000000 : ℝ)|=(1403015489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462308327/10000000000 : ℝ)|^67 ≤ (45183974902081/100000000000000 : ℝ)^51
        have hw : |(5462308327/10000000000 : ℝ)|=(5462308327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-146198871/1000000000 : ℝ)|^67 ≤ (7997710357849/100000000000000 : ℝ)^51
        have hw : |(-146198871/1000000000 : ℝ)|=(146198871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s3_s3_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1721929383/10000000000 : ℝ)*x 0 + (1142057/3200000 : ℝ)*x 1 + (-3570548543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1721929383/10000000000 : ℝ)^67 ≤ (198318792563/2000000000000 : ℝ)^51 := by
    have hnat : (1721929383 : ℕ)^67*2000000000000^51 ≤ 198318792563^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1721929383 10000000000 198318792563 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1142057/3200000 : ℝ)^67 ≤ (5166393721761/20000000000000 : ℝ)^51 := by
    have hnat : (1142057 : ℕ)^67*20000000000000^51 ≤ 5166393721761^51*3200000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142057 3200000 5166393721761 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3570548543/5000000000 : ℝ)^67 ≤ (2007877867233/3125000000000 : ℝ)^51 := by
    have hnat : (3570548543 : ℕ)^67*3125000000000^51 ≤ 2007877867233^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3570548543 5000000000 2007877867233 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1721929383/10000000000 : ℝ), (1142057/3200000 : ℝ), (-3570548543/5000000000 : ℝ)] ![(198318792563/2000000000000 : ℝ), (5166393721761/20000000000000 : ℝ), (2007877867233/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1721929383/10000000000 : ℝ)|^67 ≤ (198318792563/2000000000000 : ℝ)^51
        have hw : |(-1721929383/10000000000 : ℝ)|=(1721929383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1142057/3200000 : ℝ)|^67 ≤ (5166393721761/20000000000000 : ℝ)^51
        have hw : |(1142057/3200000 : ℝ)|=(1142057/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3570548543/5000000000 : ℝ)|^67 ≤ (2007877867233/3125000000000 : ℝ)^51
        have hw : |(-3570548543/5000000000 : ℝ)|=(3570548543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s3_s3_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (819245807/2000000000 : ℝ)*x 0 + (-1590778967/5000000000 : ℝ)*x 1 + (-2806502201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (819245807/2000000000 : ℝ)^67 ≤ (15479227708639/50000000000000 : ℝ)^51 := by
    have hnat : (819245807 : ℕ)^67*50000000000000^51 ≤ 15479227708639^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819245807 2000000000 15479227708639 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1590778967/5000000000 : ℝ)^67 ≤ (5553225167297/25000000000000 : ℝ)^51 := by
    have hnat : (1590778967 : ℕ)^67*25000000000000^51 ≤ 5553225167297^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590778967 5000000000 5553225167297 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2806502201/5000000000 : ℝ)^67 ≤ (46828643901743/100000000000000 : ℝ)^51 := by
    have hnat : (2806502201 : ℕ)^67*100000000000000^51 ≤ 46828643901743^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806502201 5000000000 46828643901743 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(819245807/2000000000 : ℝ), (-1590778967/5000000000 : ℝ), (-2806502201/5000000000 : ℝ)] ![(15479227708639/50000000000000 : ℝ), (5553225167297/25000000000000 : ℝ), (46828643901743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(819245807/2000000000 : ℝ)|^67 ≤ (15479227708639/50000000000000 : ℝ)^51
        have hw : |(819245807/2000000000 : ℝ)|=(819245807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1590778967/5000000000 : ℝ)|^67 ≤ (5553225167297/25000000000000 : ℝ)^51
        have hw : |(-1590778967/5000000000 : ℝ)|=(1590778967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2806502201/5000000000 : ℝ)|^67 ≤ (46828643901743/100000000000000 : ℝ)^51
        have hw : |(-2806502201/5000000000 : ℝ)|=(2806502201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s3_s3_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2851116329/5000000000 : ℝ)*x 0 + (1320427741/2500000000 : ℝ)*x 1 + (796979481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2851116329/5000000000 : ℝ)^67 ≤ (47809038559987/100000000000000 : ℝ)^51 := by
    have hnat : (2851116329 : ℕ)^67*100000000000000^51 ≤ 47809038559987^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2851116329 5000000000 47809038559987 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320427741/2500000000 : ℝ)^67 ≤ (43231665445389/100000000000000 : ℝ)^51 := by
    have hnat : (1320427741 : ℕ)^67*100000000000000^51 ≤ 43231665445389^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320427741 2500000000 43231665445389 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796979481/5000000000 : ℝ)^67 ≤ (4479647991783/50000000000000 : ℝ)^51 := by
    have hnat : (796979481 : ℕ)^67*50000000000000^51 ≤ 4479647991783^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796979481 5000000000 4479647991783 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2851116329/5000000000 : ℝ), (1320427741/2500000000 : ℝ), (796979481/5000000000 : ℝ)] ![(47809038559987/100000000000000 : ℝ), (43231665445389/100000000000000 : ℝ), (4479647991783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2851116329/5000000000 : ℝ)|^67 ≤ (47809038559987/100000000000000 : ℝ)^51
        have hw : |(2851116329/5000000000 : ℝ)|=(2851116329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320427741/2500000000 : ℝ)|^67 ≤ (43231665445389/100000000000000 : ℝ)^51
        have hw : |(1320427741/2500000000 : ℝ)|=(1320427741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(796979481/5000000000 : ℝ)|^67 ≤ (4479647991783/50000000000000 : ℝ)^51
        have hw : |(796979481/5000000000 : ℝ)|=(796979481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s3_s3_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6984456331/10000000000 : ℝ)*x 0 + (2010167757/5000000000 : ℝ)*x 1 + (-688028449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6984456331/10000000000 : ℝ)^67 ≤ (62406960625489/100000000000000 : ℝ)^51 := by
    have hnat : (6984456331 : ℕ)^67*100000000000000^51 ≤ 62406960625489^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6984456331 10000000000 62406960625489 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010167757/5000000000 : ℝ)^67 ≤ (30207118122657/100000000000000 : ℝ)^51 := by
    have hnat : (2010167757 : ℕ)^67*100000000000000^51 ≤ 30207118122657^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010167757 5000000000 30207118122657 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (688028449/5000000000 : ℝ)^67 ≤ (7385921227469/100000000000000 : ℝ)^51 := by
    have hnat : (688028449 : ℕ)^67*100000000000000^51 ≤ 7385921227469^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688028449 5000000000 7385921227469 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6984456331/10000000000 : ℝ), (2010167757/5000000000 : ℝ), (-688028449/5000000000 : ℝ)] ![(62406960625489/100000000000000 : ℝ), (30207118122657/100000000000000 : ℝ), (7385921227469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6984456331/10000000000 : ℝ)|^67 ≤ (62406960625489/100000000000000 : ℝ)^51
        have hw : |(6984456331/10000000000 : ℝ)|=(6984456331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2010167757/5000000000 : ℝ)|^67 ≤ (30207118122657/100000000000000 : ℝ)^51
        have hw : |(2010167757/5000000000 : ℝ)|=(2010167757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-688028449/5000000000 : ℝ)|^67 ≤ (7385921227469/100000000000000 : ℝ)^51
        have hw : |(-688028449/5000000000 : ℝ)|=(688028449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s3_s3_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1509671663/10000000000 : ℝ)*x 0 + (4322356017/10000000000 : ℝ)*x 1 + (-6643440791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1509671663/10000000000 : ℝ)^67 ≤ (1042766395761/12500000000000 : ℝ)^51 := by
    have hnat : (1509671663 : ℕ)^67*12500000000000^51 ≤ 1042766395761^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1509671663 10000000000 1042766395761 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4322356017/10000000000 : ℝ)^67 ≤ (16611421033447/50000000000000 : ℝ)^51 := by
    have hnat : (4322356017 : ℕ)^67*50000000000000^51 ≤ 16611421033447^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322356017 10000000000 16611421033447 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6643440791/10000000000 : ℝ)^67 ≤ (29217513374931/50000000000000 : ℝ)^51 := by
    have hnat : (6643440791 : ℕ)^67*50000000000000^51 ≤ 29217513374931^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6643440791 10000000000 29217513374931 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1509671663/10000000000 : ℝ), (4322356017/10000000000 : ℝ), (-6643440791/10000000000 : ℝ)] ![(1042766395761/12500000000000 : ℝ), (16611421033447/50000000000000 : ℝ), (29217513374931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1509671663/10000000000 : ℝ)|^67 ≤ (1042766395761/12500000000000 : ℝ)^51
        have hw : |(-1509671663/10000000000 : ℝ)|=(1509671663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4322356017/10000000000 : ℝ)|^67 ≤ (16611421033447/50000000000000 : ℝ)^51
        have hw : |(4322356017/10000000000 : ℝ)|=(4322356017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6643440791/10000000000 : ℝ)|^67 ≤ (29217513374931/50000000000000 : ℝ)^51
        have hw : |(-6643440791/10000000000 : ℝ)|=(6643440791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s3_s3_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1134546463/2000000000 : ℝ)*x 0 + (-2919459377/10000000000 : ℝ)*x 1 + (-4268000177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1134546463/2000000000 : ℝ)^67 ≤ (9496873471893/20000000000000 : ℝ)^51 := by
    have hnat : (1134546463 : ℕ)^67*20000000000000^51 ≤ 9496873471893^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134546463 2000000000 9496873471893 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2919459377/10000000000 : ℝ)^67 ≤ (19840571671217/100000000000000 : ℝ)^51 := by
    have hnat : (2919459377 : ℕ)^67*100000000000000^51 ≤ 19840571671217^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2919459377 10000000000 19840571671217 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4268000177/10000000000 : ℝ)^67 ≤ (1633753047709/5000000000000 : ℝ)^51 := by
    have hnat : (4268000177 : ℕ)^67*5000000000000^51 ≤ 1633753047709^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268000177 10000000000 1633753047709 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1134546463/2000000000 : ℝ), (-2919459377/10000000000 : ℝ), (-4268000177/10000000000 : ℝ)] ![(9496873471893/20000000000000 : ℝ), (19840571671217/100000000000000 : ℝ), (1633753047709/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1134546463/2000000000 : ℝ)|^67 ≤ (9496873471893/20000000000000 : ℝ)^51
        have hw : |(1134546463/2000000000 : ℝ)|=(1134546463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2919459377/10000000000 : ℝ)|^67 ≤ (19840571671217/100000000000000 : ℝ)^51
        have hw : |(-2919459377/10000000000 : ℝ)|=(2919459377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4268000177/10000000000 : ℝ)|^67 ≤ (1633753047709/5000000000000 : ℝ)^51
        have hw : |(-4268000177/10000000000 : ℝ)|=(4268000177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s3_s3_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4228442229/10000000000 : ℝ)*x 0 + (149836481/250000000 : ℝ)*x 1 + (2558236951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4228442229/10000000000 : ℝ)^67 ≤ (16138890276311/50000000000000 : ℝ)^51 := by
    have hnat : (4228442229 : ℕ)^67*50000000000000^51 ≤ 16138890276311^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228442229 10000000000 16138890276311 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149836481/250000000 : ℝ)^67 ≤ (51042194542987/100000000000000 : ℝ)^51 := by
    have hnat : (149836481 : ℕ)^67*100000000000000^51 ≤ 51042194542987^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149836481 250000000 51042194542987 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2558236951/10000000000 : ℝ)^67 ≤ (1042501556311/6250000000000 : ℝ)^51 := by
    have hnat : (2558236951 : ℕ)^67*6250000000000^51 ≤ 1042501556311^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2558236951 10000000000 1042501556311 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4228442229/10000000000 : ℝ), (149836481/250000000 : ℝ), (2558236951/10000000000 : ℝ)] ![(16138890276311/50000000000000 : ℝ), (51042194542987/100000000000000 : ℝ), (1042501556311/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4228442229/10000000000 : ℝ)|^67 ≤ (16138890276311/50000000000000 : ℝ)^51
        have hw : |(4228442229/10000000000 : ℝ)|=(4228442229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(149836481/250000000 : ℝ)|^67 ≤ (51042194542987/100000000000000 : ℝ)^51
        have hw : |(149836481/250000000 : ℝ)|=(149836481/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2558236951/10000000000 : ℝ)|^67 ≤ (1042501556311/6250000000000 : ℝ)^51
        have hw : |(2558236951/10000000000 : ℝ)|=(2558236951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s3_s3_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3600863829/5000000000 : ℝ)*x 0 + (3583156299/10000000000 : ℝ)*x 1 + (-1607975789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3600863829/5000000000 : ℝ)^67 ≤ (64969713390859/100000000000000 : ℝ)^51 := by
    have hnat : (3600863829 : ℕ)^67*100000000000000^51 ≤ 64969713390859^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3600863829 5000000000 64969713390859 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3583156299/10000000000 : ℝ)^67 ≤ (1622959098019/6250000000000 : ℝ)^51 := by
    have hnat : (3583156299 : ℕ)^67*6250000000000^51 ≤ 1622959098019^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3583156299 10000000000 1622959098019 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1607975789/10000000000 : ℝ)^67 ≤ (9062941028767/100000000000000 : ℝ)^51 := by
    have hnat : (1607975789 : ℕ)^67*100000000000000^51 ≤ 9062941028767^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1607975789 10000000000 9062941028767 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3600863829/5000000000 : ℝ), (3583156299/10000000000 : ℝ), (-1607975789/10000000000 : ℝ)] ![(64969713390859/100000000000000 : ℝ), (1622959098019/6250000000000 : ℝ), (9062941028767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3600863829/5000000000 : ℝ)|^67 ≤ (64969713390859/100000000000000 : ℝ)^51
        have hw : |(3600863829/5000000000 : ℝ)|=(3600863829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3583156299/10000000000 : ℝ)|^67 ≤ (1622959098019/6250000000000 : ℝ)^51
        have hw : |(3583156299/10000000000 : ℝ)|=(3583156299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1607975789/10000000000 : ℝ)|^67 ≤ (9062941028767/100000000000000 : ℝ)^51
        have hw : |(-1607975789/10000000000 : ℝ)|=(1607975789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302052_s3 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((54459/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(54459/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29087/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29087/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38241/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38241/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3333/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3333/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7203/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7203/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11291/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11291/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s3_pow0 : (54459/100000 : ℝ) ^ (65/16 : ℝ) ≤ (8468042000160462497/100000000000000000000 : ℝ) := by
    have hpowers : (54459/100000 : ℝ)^65 ≤ (8468042000160462497/100000000000000000000 : ℝ)^16 := by
      have hnat : (54459 : ℕ)^65*100000000000000000000^16 ≤ 8468042000160462497^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54459 100000 8468042000160462497 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (54459/100000 : ℝ)) (X := (8468042000160462497/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (108468042000160462497/100000000000000000000 : ℝ) ≤ (318815696843737/312500000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (108468042000160462497/100000000000000000000 : ℝ)^16 ≤ (318815696843737/312500000000000 : ℝ)^65 := by
      have hnat : (108468042000160462497 : ℕ)^16*312500000000000^65 ≤ 318815696843737^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108468042000160462497 100000000000000000000 318815696843737 312500000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (318815696843737/312500000000000 : ℝ)) (X := (108468042000160462497/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (58468042000160462497/50000000000000000000 : ℝ) ≤ (10392637901123733/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (58468042000160462497/50000000000000000000 : ℝ)^16 ≤ (10392637901123733/10000000000000000 : ℝ)^65 := by
      have hnat : (58468042000160462497 : ℕ)^16*10000000000000000^65 ≤ 10392637901123733^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58468042000160462497 50000000000000000000 10392637901123733 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10392637901123733/10000000000000000 : ℝ)) (X := (58468042000160462497/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(6315696843737/170184375000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(190535602124149/5445900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (54459/100000 : ℝ)) (alpha := (6315696843737/170184375000000 : ℝ)) (beta := (190535602124149/5445900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (54459/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(6315696843737/170184375000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(190535602124149/5445900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (29087/50000 : ℝ) ^ (65/16 : ℝ) ≤ (5535811181948911517/50000000000000000000 : ℝ) := by
    have hpowers : (29087/50000 : ℝ)^65 ≤ (5535811181948911517/50000000000000000000 : ℝ)^16 := by
      have hnat : (29087 : ℕ)^65*50000000000000000000^16 ≤ 5535811181948911517^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29087 50000 5535811181948911517 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29087/50000 : ℝ)) (X := (5535811181948911517/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (55535811181948911517/50000000000000000000 : ℝ) ≤ (320682605808569/312500000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (55535811181948911517/50000000000000000000 : ℝ)^16 ≤ (320682605808569/312500000000000 : ℝ)^65 := by
      have hnat : (55535811181948911517 : ℕ)^16*312500000000000^65 ≤ 320682605808569^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55535811181948911517 50000000000000000000 320682605808569 312500000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (320682605808569/312500000000000 : ℝ)) (X := (55535811181948911517/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (30535811181948911517/25000000000000000000 : ℝ) ≤ (10504690224866309/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (30535811181948911517/25000000000000000000 : ℝ)^16 ≤ (10504690224866309/10000000000000000 : ℝ)^65 := by
      have hnat : (30535811181948911517 : ℕ)^16*10000000000000000^65 ≤ 10504690224866309^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30535811181948911517 25000000000000000000 10504690224866309 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10504690224866309/10000000000000000 : ℝ)) (X := (30535811181948911517/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(8182605808569/181793750000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(242846838992101/5817400000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (29087/50000 : ℝ)) (alpha := (8182605808569/181793750000000 : ℝ)) (beta := (242846838992101/5817400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (29087/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(8182605808569/181793750000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(242846838992101/5817400000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (38241/100000 : ℝ) ^ (65/16 : ℝ) ≤ (80553614253442421/4000000000000000000 : ℝ) := by
    have hpowers : (38241/100000 : ℝ)^65 ≤ (80553614253442421/4000000000000000000 : ℝ)^16 := by
      have hnat : (38241 : ℕ)^65*4000000000000000000^16 ≤ 80553614253442421^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38241 100000 80553614253442421 4000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38241/100000 : ℝ)) (X := (80553614253442421/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (4080553614253442421/4000000000000000000 : ℝ) ≤ (5024599772952139/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (4080553614253442421/4000000000000000000 : ℝ)^16 ≤ (5024599772952139/5000000000000000 : ℝ)^65 := by
      have hnat : (4080553614253442421 : ℕ)^16*5000000000000000^65 ≤ 5024599772952139^65*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4080553614253442421 4000000000000000000 5024599772952139 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5024599772952139/5000000000000000 : ℝ)) (X := (4080553614253442421/4000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (2080553614253442421/2000000000000000000 : ℝ) ≤ (5048836140954761/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2080553614253442421/2000000000000000000 : ℝ)^16 ≤ (5048836140954761/5000000000000000 : ℝ)^65 := by
      have hnat : (2080553614253442421 : ℕ)^16*5000000000000000^65 ≤ 5048836140954761^65*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2080553614253442421 2000000000000000000 5048836140954761 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5048836140954761/5000000000000000 : ℝ)) (X := (2080553614253442421/2000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(3514253278877/273150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(12118184001311/956025000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (38241/100000 : ℝ)) (alpha := (3514253278877/273150000000000 : ℝ)) (beta := (12118184001311/956025000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (38241/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(3514253278877/273150000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(12118184001311/956025000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-2515705299/10000000000 : ℝ)*X 0 0+(1820937819/5000000000 : ℝ)*X 0 1+(-1633104911/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((577728207/1250000000 : ℝ)*X 1 0+(-177734571/500000000 : ℝ)*X 1 1+(-4790094033/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((486206669/1000000000 : ℝ)*X 2 0+(5548365829/10000000000 : ℝ)*X 2 1+(592961487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((5884366667/10000000000 : ℝ)*X 0 0+(879351699/2000000000 : ℝ)*X 0 1+(-2501847493/10000000000 : ℝ)*X 0 2+(5884366667/10000000000 : ℝ)*X 1 0+(879351699/2000000000 : ℝ)*X 1 1+(-2501847493/10000000000 : ℝ)*X 1 2+(5884366667/10000000000 : ℝ)*X 2 0+(879351699/2000000000 : ℝ)*X 2 1+(-2501847493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1197117477/5000000000 : ℝ)*X 0 0+(304511739/1000000000 : ℝ)*X 0 1+(-3548886023/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((1081548737/2500000000 : ℝ)*X 1 0+(-351328047/1250000000 : ℝ)*X 1 1+(-713400109/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((4567954033/10000000000 : ℝ)*X 2 0+(1608023279/2500000000 : ℝ)*X 2 1+(37494061/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((1403015489/2500000000 : ℝ)*X 0 0+(5462308327/10000000000 : ℝ)*X 0 1+(-146198871/1000000000 : ℝ)*X 0 2+(1403015489/2500000000 : ℝ)*X 1 0+(5462308327/10000000000 : ℝ)*X 1 1+(-146198871/1000000000 : ℝ)*X 1 2+(1403015489/2500000000 : ℝ)*X 2 0+(5462308327/10000000000 : ℝ)*X 2 1+(-146198871/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1721929383/10000000000 : ℝ)*X 0 0+(1142057/3200000 : ℝ)*X 0 1+(-3570548543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((819245807/2000000000 : ℝ)*X 1 0+(-1590778967/5000000000 : ℝ)*X 1 1+(-2806502201/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((2851116329/5000000000 : ℝ)*X 2 0+(1320427741/2500000000 : ℝ)*X 2 1+(796979481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((6984456331/10000000000 : ℝ)*X 0 0+(2010167757/5000000000 : ℝ)*X 0 1+(-688028449/5000000000 : ℝ)*X 0 2+(6984456331/10000000000 : ℝ)*X 1 0+(2010167757/5000000000 : ℝ)*X 1 1+(-688028449/5000000000 : ℝ)*X 1 2+(6984456331/10000000000 : ℝ)*X 2 0+(2010167757/5000000000 : ℝ)*X 2 1+(-688028449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-1509671663/10000000000 : ℝ)*X 0 0+(4322356017/10000000000 : ℝ)*X 0 1+(-6643440791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((1134546463/2000000000 : ℝ)*X 1 0+(-2919459377/10000000000 : ℝ)*X 1 1+(-4268000177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((4228442229/10000000000 : ℝ)*X 2 0+(149836481/250000000 : ℝ)*X 2 1+(2558236951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((3600863829/5000000000 : ℝ)*X 0 0+(3583156299/10000000000 : ℝ)*X 0 1+(-1607975789/10000000000 : ℝ)*X 0 2+(3600863829/5000000000 : ℝ)*X 1 0+(3583156299/10000000000 : ℝ)*X 1 1+(-1607975789/10000000000 : ℝ)*X 1 2+(3600863829/5000000000 : ℝ)*X 2 0+(3583156299/10000000000 : ℝ)*X 2 1+(-1607975789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((3333/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3333/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4017422587571104639273069/771320970000000000000000000000 : ℝ) := by norm_num
    linear_combination (586897626973/1000000000000 : ℝ)*(base39) + (383151/1000000000000 : ℝ)*(base50) + (586718020013/500000000000 : ℝ)*(base59) + (542608251491/100000000000 : ℝ)*(major_s3_0) + (542608251491/100000000000 : ℝ)*(major_s3_1) + (542608251491/100000000000 : ℝ)*(major_s3_2) + (11102371/500000000000 : ℝ)*(sp_s3_1) + (479133/100000000000 : ℝ)*(sp_s3_6) + (450915460139/62500000000 : ℝ)*(sp_s3_7) + (3607274566281/500000000000 : ℝ)*(sp_s3_8) + (721460541583/100000000000 : ℝ)*(sp_s3_9) + (3637511140097/1000000000000 : ℝ)*(sp_s3_13) + (1900623/25000000000 : ℝ)*(sp_s3_15) + (20973197/500000000000 : ℝ)*(sp_s3_23) + (3637515931427/1000000000000 : ℝ)*(f.failure) + (450915460139/62500000000 : ℝ)*(f.sum) + (7524881457063097/198627851250000000000000000000 : ℝ)*base62 + (104474278124807/382410000000000000000000000 : ℝ)*base65 + (47034434398051/116348000000000000000000000 : ℝ)*base66 + (2038300221163/6828750000000000000000000 : ℝ)*base69 + (5952673629185737/462792582000000000000000000000 : ℝ)*base71 + (14982453516209/544590000000000000000000000 : ℝ)*base73 + (35554893996609/145435000000000000000000000 : ℝ)*base75 + (142859576498513/544590000000000000000000000 : ℝ)*base77 + (6717610311199199153/31680978660000000000000000000000 : ℝ)*base79 + (3441/10000000000000000 : ℝ)*base86 + (3441/10000000000000000 : ℝ)*base88 + (3441/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7203/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7203/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (109408571704651067426883548559/24928236727100000000000000000000000 : ℝ) := by norm_num
    linear_combination (69708617763/100000000000 : ℝ)*(base39) + (900229/1000000000000 : ℝ)*(base49) + (981014028283/1000000000000 : ℝ)*(base59) + (5512884644439/1000000000000 : ℝ)*(major_s3_0) + (5512884644439/1000000000000 : ℝ)*(major_s3_1) + (5512884644439/1000000000000 : ℝ)*(major_s3_2) + (7925849/1000000000000 : ℝ)*(sp_s3_6) + (102801/6250000000 : ℝ)*(sp_s3_7) + (4507813/250000000000 : ℝ)*(sp_s3_8) + (7330045374891/1000000000000 : ℝ)*(sp_s3_14) + (7330043791799/1000000000000 : ℝ)*(sp_s3_15) + (7330061823051/1000000000000 : ℝ)*(sp_s3_16) + (1847825102299/500000000000 : ℝ)*(sp_s3_20) + (23936197/500000000000 : ℝ)*(sp_s3_27) + (1847853001421/500000000000 : ℝ)*(f.failure) + (7330061823051/1000000000000 : ℝ)*(f.sum) + (21437190959224801/35311618000000000000000000000 : ℝ)*base63 + (42729286047239/106225000000000000000000000 : ℝ)*base65 + (1804412266582281/5817400000000000000000000000 : ℝ)*base67 + (10704664292977/30350000000000000000000000 : ℝ)*base69 + (276932442390546427/428511650000000000000000000000 : ℝ)*base71 + (51812914421523/201700000000000000000000000 : ℝ)*base73 + (443391252943843/1454350000000000000000000000 : ℝ)*base75 + (7544252590799/100850000000000000000000000 : ℝ)*base77 + (1722203571113004919/11733695800000000000000000000000 : ℝ)*base79 + (2057/5000000000000000 : ℝ)*base87 + (2057/5000000000000000 : ℝ)*base89 + (2057/5000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11291/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11291/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (64112140626299393520329733703/4985647345420000000000000000000000 : ℝ) := by norm_num
    linear_combination (1066615794827/1000000000000 : ℝ)*(base39) + (2592129/500000000000 : ℝ)*(base40) + (384527039489/500000000000 : ℝ)*(base59) + (4460714232339/1000000000000 : ℝ)*(major_s3_0) + (4460714232339/1000000000000 : ℝ)*(major_s3_1) + (4460714232339/1000000000000 : ℝ)*(major_s3_2) + (30924431/1000000000000 : ℝ)*(sp_s3_0) + (85906423/1000000000000 : ℝ)*(sp_s3_2) + (18778533/500000000000 : ℝ)*(sp_s3_9) + (113814083/500000000000 : ℝ)*(sp_s3_20) + (296551856417/50000000000 : ℝ)*(sp_s3_21) + (593106805277/100000000000 : ℝ)*(sp_s3_22) + (5930944589281/1000000000000 : ℝ)*(sp_s3_23) + (373766062161/125000000000 : ℝ)*(sp_s3_27) + (1495178062727/500000000000 : ℝ)*(f.failure) + (593106805277/100000000000 : ℝ)*(f.sum) + (12953965933074643/132418567500000000000000000000 : ℝ)*base62 + (129852741089719/159337500000000000000000000 : ℝ)*base64 + (4296123971084721/5817400000000000000000000000 : ℝ)*base67 + (23126813663899/91050000000000000000000000 : ℝ)*base68 + (722673359431085473/964151212500000000000000000000 : ℝ)*base70 + (1577049510157537/1815300000000000000000000000 : ℝ)*base73 + (500158706770317/1454350000000000000000000000 : ℝ)*base74 + (448782243657739/907650000000000000000000000 : ℝ)*base76 + (86486126675058402571/105603262200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (3659/5000000000000000 : ℝ)*base87 + (3659/5000000000000000 : ℝ)*base89 + (3659/5000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((54459/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(54459/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29087/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29087/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38241/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38241/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3333/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3333/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7203/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7203/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11291/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11291/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302052_s3 p hpa hpb X hX hprev2

#print axioms solution

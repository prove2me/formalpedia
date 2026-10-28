-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305060_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:31:30.975425+00:00
-- url     : https://prove2.me/submissions/893905ea-1691-44f2-a6c2-0205f840a449

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
theorem collision_support_c305060_s3_s3_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-936186787/5000000000 : ℝ)*x 0 + (1107639897/2500000000 : ℝ)*x 1 + (-3154921987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (936186787/5000000000 : ℝ)^67 ≤ (1106938478661/10000000000000 : ℝ)^51 := by
    have hnat : (936186787 : ℕ)^67*10000000000000^51 ≤ 1106938478661^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936186787 5000000000 1106938478661 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107639897/2500000000 : ℝ)^67 ≤ (17159855702277/50000000000000 : ℝ)^51 := by
    have hnat : (1107639897 : ℕ)^67*50000000000000^51 ≤ 17159855702277^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107639897 2500000000 17159855702277 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154921987/5000000000 : ℝ)^67 ≤ (54610903797141/100000000000000 : ℝ)^51 := by
    have hnat : (3154921987 : ℕ)^67*100000000000000^51 ≤ 54610903797141^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154921987 5000000000 54610903797141 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-936186787/5000000000 : ℝ), (1107639897/2500000000 : ℝ), (-3154921987/5000000000 : ℝ)] ![(1106938478661/10000000000000 : ℝ), (17159855702277/50000000000000 : ℝ), (54610903797141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-936186787/5000000000 : ℝ)|^67 ≤ (1106938478661/10000000000000 : ℝ)^51
        have hw : |(-936186787/5000000000 : ℝ)|=(936186787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1107639897/2500000000 : ℝ)|^67 ≤ (17159855702277/50000000000000 : ℝ)^51
        have hw : |(1107639897/2500000000 : ℝ)|=(1107639897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3154921987/5000000000 : ℝ)|^67 ≤ (54610903797141/100000000000000 : ℝ)^51
        have hw : |(-3154921987/5000000000 : ℝ)|=(3154921987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s3_s3_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2242865087/5000000000 : ℝ)*x 0 + (-974940723/5000000000 : ℝ)*x 1 + (-9930913/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2242865087/5000000000 : ℝ)^67 ≤ (272517477183/781250000000 : ℝ)^51 := by
    have hnat : (2242865087 : ℕ)^67*781250000000^51 ≤ 272517477183^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242865087 5000000000 272517477183 781250000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (974940723/5000000000 : ℝ)^67 ≤ (5837618206953/50000000000000 : ℝ)^51 := by
    have hnat : (974940723 : ℕ)^67*50000000000000^51 ≤ 5837618206953^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974940723 5000000000 5837618206953 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9930913/16000000 : ℝ)^67 ≤ (53442526485887/100000000000000 : ℝ)^51 := by
    have hnat : (9930913 : ℕ)^67*100000000000000^51 ≤ 53442526485887^51*16000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9930913 16000000 53442526485887 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2242865087/5000000000 : ℝ), (-974940723/5000000000 : ℝ), (-9930913/16000000 : ℝ)] ![(272517477183/781250000000 : ℝ), (5837618206953/50000000000000 : ℝ), (53442526485887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2242865087/5000000000 : ℝ)|^67 ≤ (272517477183/781250000000 : ℝ)^51
        have hw : |(2242865087/5000000000 : ℝ)|=(2242865087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-974940723/5000000000 : ℝ)|^67 ≤ (5837618206953/50000000000000 : ℝ)^51
        have hw : |(-974940723/5000000000 : ℝ)|=(974940723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9930913/16000000 : ℝ)|^67 ≤ (53442526485887/100000000000000 : ℝ)^51
        have hw : |(-9930913/16000000 : ℝ)|=(9930913/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s3_s3_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-399377501/2000000000 : ℝ)*x 0 + (2857154983/10000000000 : ℝ)*x 1 + (-7511655771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399377501/2000000000 : ℝ)^67 ≤ (12046383627743/100000000000000 : ℝ)^51 := by
    have hnat : (399377501 : ℕ)^67*100000000000000^51 ≤ 12046383627743^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399377501 2000000000 12046383627743 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2857154983/10000000000 : ℝ)^67 ≤ (9643093272549/50000000000000 : ℝ)^51 := by
    have hnat : (2857154983 : ℕ)^67*50000000000000^51 ≤ 9643093272549^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2857154983 10000000000 9643093272549 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7511655771/10000000000 : ℝ)^67 ≤ (13733485964259/20000000000000 : ℝ)^51 := by
    have hnat : (7511655771 : ℕ)^67*20000000000000^51 ≤ 13733485964259^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7511655771 10000000000 13733485964259 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399377501/2000000000 : ℝ), (2857154983/10000000000 : ℝ), (-7511655771/10000000000 : ℝ)] ![(12046383627743/100000000000000 : ℝ), (9643093272549/50000000000000 : ℝ), (13733485964259/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399377501/2000000000 : ℝ)|^67 ≤ (12046383627743/100000000000000 : ℝ)^51
        have hw : |(-399377501/2000000000 : ℝ)|=(399377501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2857154983/10000000000 : ℝ)|^67 ≤ (9643093272549/50000000000000 : ℝ)^51
        have hw : |(2857154983/10000000000 : ℝ)|=(2857154983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7511655771/10000000000 : ℝ)|^67 ≤ (13733485964259/20000000000000 : ℝ)^51
        have hw : |(-7511655771/10000000000 : ℝ)|=(7511655771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s3_s3_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3182539843/10000000000 : ℝ)*x 0 + (-1592091541/10000000000 : ℝ)*x 1 + (-752540391/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3182539843/10000000000 : ℝ)^67 ≤ (11110953649667/50000000000000 : ℝ)^51 := by
    have hnat : (3182539843 : ℕ)^67*50000000000000^51 ≤ 11110953649667^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3182539843 10000000000 11110953649667 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1592091541/10000000000 : ℝ)^67 ≤ (8945509174137/100000000000000 : ℝ)^51 := by
    have hnat : (1592091541 : ℕ)^67*100000000000000^51 ≤ 8945509174137^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592091541 10000000000 8945509174137 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (752540391/1000000000 : ℝ)^67 ≤ (4302036469183/6250000000000 : ℝ)^51 := by
    have hnat : (752540391 : ℕ)^67*6250000000000^51 ≤ 4302036469183^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752540391 1000000000 4302036469183 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3182539843/10000000000 : ℝ), (-1592091541/10000000000 : ℝ), (-752540391/1000000000 : ℝ)] ![(11110953649667/50000000000000 : ℝ), (8945509174137/100000000000000 : ℝ), (4302036469183/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3182539843/10000000000 : ℝ)|^67 ≤ (11110953649667/50000000000000 : ℝ)^51
        have hw : |(3182539843/10000000000 : ℝ)|=(3182539843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1592091541/10000000000 : ℝ)|^67 ≤ (8945509174137/100000000000000 : ℝ)^51
        have hw : |(-1592091541/10000000000 : ℝ)|=(1592091541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-752540391/1000000000 : ℝ)|^67 ≤ (4302036469183/6250000000000 : ℝ)^51
        have hw : |(-752540391/1000000000 : ℝ)|=(752540391/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s3_s3_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3480277069/10000000000 : ℝ)*x 0 + (7310792993/10000000000 : ℝ)*x 1 + (782244081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3480277069/10000000000 : ℝ)^67 ≤ (24992309532267/100000000000000 : ℝ)^51 := by
    have hnat : (3480277069 : ℕ)^67*100000000000000^51 ≤ 24992309532267^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3480277069 10000000000 24992309532267 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7310792993/10000000000 : ℝ)^67 ≤ (66265377880689/100000000000000 : ℝ)^51 := by
    have hnat : (7310792993 : ℕ)^67*100000000000000^51 ≤ 66265377880689^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7310792993 10000000000 66265377880689 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (782244081/5000000000 : ℝ)^67 ≤ (8742312576029/100000000000000 : ℝ)^51 := by
    have hnat : (782244081 : ℕ)^67*100000000000000^51 ≤ 8742312576029^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782244081 5000000000 8742312576029 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3480277069/10000000000 : ℝ), (7310792993/10000000000 : ℝ), (782244081/5000000000 : ℝ)] ![(24992309532267/100000000000000 : ℝ), (66265377880689/100000000000000 : ℝ), (8742312576029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3480277069/10000000000 : ℝ)|^67 ≤ (24992309532267/100000000000000 : ℝ)^51
        have hw : |(3480277069/10000000000 : ℝ)|=(3480277069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7310792993/10000000000 : ℝ)|^67 ≤ (66265377880689/100000000000000 : ℝ)^51
        have hw : |(7310792993/10000000000 : ℝ)|=(7310792993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(782244081/5000000000 : ℝ)|^67 ≤ (8742312576029/100000000000000 : ℝ)^51
        have hw : |(782244081/5000000000 : ℝ)|=(782244081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s3_s3_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2575456227/5000000000 : ℝ)*x 0 + (6620434411/10000000000 : ℝ)*x 1 + (117/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2575456227/5000000000 : ℝ)^67 ≤ (20425135007/48828125000 : ℝ)^51 := by
    have hnat : (2575456227 : ℕ)^67*48828125000^51 ≤ 20425135007^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575456227 5000000000 20425135007 48828125000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6620434411/10000000000 : ℝ)^67 ≤ (11633864692773/20000000000000 : ℝ)^51 := by
    have hnat : (6620434411 : ℕ)^67*20000000000000^51 ≤ 11633864692773^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6620434411 10000000000 11633864692773 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117/2000000000 : ℝ)^67 ≤ (787/2500000000000 : ℝ)^51 := by
    have hnat : (117 : ℕ)^67*2500000000000^51 ≤ 787^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117 2000000000 787 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2575456227/5000000000 : ℝ), (6620434411/10000000000 : ℝ), (117/2000000000 : ℝ)] ![(20425135007/48828125000 : ℝ), (11633864692773/20000000000000 : ℝ), (787/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2575456227/5000000000 : ℝ)|^67 ≤ (20425135007/48828125000 : ℝ)^51
        have hw : |(2575456227/5000000000 : ℝ)|=(2575456227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6620434411/10000000000 : ℝ)|^67 ≤ (11633864692773/20000000000000 : ℝ)^51
        have hw : |(6620434411/10000000000 : ℝ)|=(6620434411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(117/2000000000 : ℝ)|^67 ≤ (787/2500000000000 : ℝ)^51
        have hw : |(117/2000000000 : ℝ)|=(117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s3_s3_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-188370391/1250000000 : ℝ)*x 0 + (2920118787/10000000000 : ℝ)*x 1 + (-7773664467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (188370391/1250000000 : ℝ)^67 ≤ (4161237217461/50000000000000 : ℝ)^51 := by
    have hnat : (188370391 : ℕ)^67*50000000000000^51 ≤ 4161237217461^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188370391 1250000000 4161237217461 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2920118787/10000000000 : ℝ)^67 ≤ (19846459121957/100000000000000 : ℝ)^51 := by
    have hnat : (2920118787 : ℕ)^67*100000000000000^51 ≤ 19846459121957^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2920118787 10000000000 19846459121957 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7773664467/10000000000 : ℝ)^67 ≤ (17957766605033/25000000000000 : ℝ)^51 := by
    have hnat : (7773664467 : ℕ)^67*25000000000000^51 ≤ 17957766605033^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7773664467 10000000000 17957766605033 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-188370391/1250000000 : ℝ), (2920118787/10000000000 : ℝ), (-7773664467/10000000000 : ℝ)] ![(4161237217461/50000000000000 : ℝ), (19846459121957/100000000000000 : ℝ), (17957766605033/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-188370391/1250000000 : ℝ)|^67 ≤ (4161237217461/50000000000000 : ℝ)^51
        have hw : |(-188370391/1250000000 : ℝ)|=(188370391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2920118787/10000000000 : ℝ)|^67 ≤ (19846459121957/100000000000000 : ℝ)^51
        have hw : |(2920118787/10000000000 : ℝ)|=(2920118787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7773664467/10000000000 : ℝ)|^67 ≤ (17957766605033/25000000000000 : ℝ)^51
        have hw : |(-7773664467/10000000000 : ℝ)|=(7773664467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s3_s3_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (622076071/2500000000 : ℝ)*x 0 + (-1979978099/10000000000 : ℝ)*x 1 + (-3893947221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (622076071/2500000000 : ℝ)^67 ≤ (804179535307/5000000000000 : ℝ)^51 := by
    have hnat : (622076071 : ℕ)^67*5000000000000^51 ≤ 804179535307^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622076071 2500000000 804179535307 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1979978099/10000000000 : ℝ)^67 ≤ (11912552329529/100000000000000 : ℝ)^51 := by
    have hnat : (1979978099 : ℕ)^67*100000000000000^51 ≤ 11912552329529^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979978099 10000000000 11912552329529 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3893947221/5000000000 : ℝ)^67 ≤ (18000964235967/25000000000000 : ℝ)^51 := by
    have hnat : (3893947221 : ℕ)^67*25000000000000^51 ≤ 18000964235967^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3893947221 5000000000 18000964235967 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(622076071/2500000000 : ℝ), (-1979978099/10000000000 : ℝ), (-3893947221/5000000000 : ℝ)] ![(804179535307/5000000000000 : ℝ), (11912552329529/100000000000000 : ℝ), (18000964235967/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(622076071/2500000000 : ℝ)|^67 ≤ (804179535307/5000000000000 : ℝ)^51
        have hw : |(622076071/2500000000 : ℝ)|=(622076071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1979978099/10000000000 : ℝ)|^67 ≤ (11912552329529/100000000000000 : ℝ)^51
        have hw : |(-1979978099/10000000000 : ℝ)|=(1979978099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3893947221/5000000000 : ℝ)|^67 ≤ (18000964235967/25000000000000 : ℝ)^51
        have hw : |(-3893947221/5000000000 : ℝ)|=(3893947221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s3_s3_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (791112497/1250000000 : ℝ)*x 0 + (459505553/1000000000 : ℝ)*x 1 + (50696177/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (791112497/1250000000 : ℝ)^67 ≤ (54827675559621/100000000000000 : ℝ)^51 := by
    have hnat : (791112497 : ℕ)^67*100000000000000^51 ≤ 54827675559621^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791112497 1250000000 54827675559621 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (459505553/1000000000 : ℝ)^67 ≤ (18001669035387/50000000000000 : ℝ)^51 := by
    have hnat : (459505553 : ℕ)^67*50000000000000^51 ≤ 18001669035387^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459505553 1000000000 18001669035387 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50696177/312500000 : ℝ)^67 ≤ (366759454153/4000000000000 : ℝ)^51 := by
    have hnat : (50696177 : ℕ)^67*4000000000000^51 ≤ 366759454153^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50696177 312500000 366759454153 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(791112497/1250000000 : ℝ), (459505553/1000000000 : ℝ), (50696177/312500000 : ℝ)] ![(54827675559621/100000000000000 : ℝ), (18001669035387/50000000000000 : ℝ), (366759454153/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(791112497/1250000000 : ℝ)|^67 ≤ (54827675559621/100000000000000 : ℝ)^51
        have hw : |(791112497/1250000000 : ℝ)|=(791112497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(459505553/1000000000 : ℝ)|^67 ≤ (18001669035387/50000000000000 : ℝ)^51
        have hw : |(459505553/1000000000 : ℝ)|=(459505553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(50696177/312500000 : ℝ)|^67 ≤ (366759454153/4000000000000 : ℝ)^51
        have hw : |(50696177/312500000 : ℝ)|=(50696177/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s3_s3_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8435923191/10000000000 : ℝ)*x 0 + (293993269/1000000000 : ℝ)*x 1 + (-1128111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8435923191/10000000000 : ℝ)^67 ≤ (79975789468331/100000000000000 : ℝ)^51 := by
    have hnat : (8435923191 : ℕ)^67*100000000000000^51 ≤ 79975789468331^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8435923191 10000000000 79975789468331 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (293993269/1000000000 : ℝ)^67 ≤ (10011779540493/50000000000000 : ℝ)^51 := by
    have hnat : (293993269 : ℕ)^67*50000000000000^51 ≤ 10011779540493^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293993269 1000000000 10011779540493 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128111/10000000000 : ℝ)^67 ≤ (130287867/20000000000000 : ℝ)^51 := by
    have hnat : (1128111 : ℕ)^67*20000000000000^51 ≤ 130287867^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128111 10000000000 130287867 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8435923191/10000000000 : ℝ), (293993269/1000000000 : ℝ), (-1128111/10000000000 : ℝ)] ![(79975789468331/100000000000000 : ℝ), (10011779540493/50000000000000 : ℝ), (130287867/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8435923191/10000000000 : ℝ)|^67 ≤ (79975789468331/100000000000000 : ℝ)^51
        have hw : |(8435923191/10000000000 : ℝ)|=(8435923191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(293993269/1000000000 : ℝ)|^67 ≤ (10011779540493/50000000000000 : ℝ)^51
        have hw : |(293993269/1000000000 : ℝ)|=(293993269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1128111/10000000000 : ℝ)|^67 ≤ (130287867/20000000000000 : ℝ)^51
        have hw : |(-1128111/10000000000 : ℝ)|=(1128111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s3_s3_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-548830631/5000000000 : ℝ)*x 0 + (5965262403/10000000000 : ℝ)*x 1 + (-5333065993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548830631/5000000000 : ℝ)^67 ≤ (5488312053961/100000000000000 : ℝ)^51 := by
    have hnat : (548830631 : ℕ)^67*100000000000000^51 ≤ 5488312053961^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548830631 5000000000 5488312053961 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5965262403/10000000000 : ℝ)^67 ≤ (50726958520379/100000000000000 : ℝ)^51 := by
    have hnat : (5965262403 : ℕ)^67*100000000000000^51 ≤ 50726958520379^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5965262403 10000000000 50726958520379 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5333065993/10000000000 : ℝ)^67 ≤ (21892364702749/50000000000000 : ℝ)^51 := by
    have hnat : (5333065993 : ℕ)^67*50000000000000^51 ≤ 21892364702749^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5333065993 10000000000 21892364702749 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548830631/5000000000 : ℝ), (5965262403/10000000000 : ℝ), (-5333065993/10000000000 : ℝ)] ![(5488312053961/100000000000000 : ℝ), (50726958520379/100000000000000 : ℝ), (21892364702749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548830631/5000000000 : ℝ)|^67 ≤ (5488312053961/100000000000000 : ℝ)^51
        have hw : |(-548830631/5000000000 : ℝ)|=(548830631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5965262403/10000000000 : ℝ)|^67 ≤ (50726958520379/100000000000000 : ℝ)^51
        have hw : |(5965262403/10000000000 : ℝ)|=(5965262403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5333065993/10000000000 : ℝ)|^67 ≤ (21892364702749/50000000000000 : ℝ)^51
        have hw : |(-5333065993/10000000000 : ℝ)|=(5333065993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s3_s3_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1506329441/2500000000 : ℝ)*x 0 + (-1182738753/10000000000 : ℝ)*x 1 + (-5217940417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1506329441/2500000000 : ℝ)^67 ≤ (25699463896283/50000000000000 : ℝ)^51 := by
    have hnat : (1506329441 : ℕ)^67*50000000000000^51 ≤ 25699463896283^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506329441 2500000000 25699463896283 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1182738753/10000000000 : ℝ)^67 ≤ (3026916383283/50000000000000 : ℝ)^51 := by
    have hnat : (1182738753 : ℕ)^67*50000000000000^51 ≤ 3026916383283^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182738753 10000000000 3026916383283 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217940417/10000000000 : ℝ)^67 ≤ (42547239427651/100000000000000 : ℝ)^51 := by
    have hnat : (5217940417 : ℕ)^67*100000000000000^51 ≤ 42547239427651^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217940417 10000000000 42547239427651 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1506329441/2500000000 : ℝ), (-1182738753/10000000000 : ℝ), (-5217940417/10000000000 : ℝ)] ![(25699463896283/50000000000000 : ℝ), (3026916383283/50000000000000 : ℝ), (42547239427651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1506329441/2500000000 : ℝ)|^67 ≤ (25699463896283/50000000000000 : ℝ)^51
        have hw : |(1506329441/2500000000 : ℝ)|=(1506329441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1182738753/10000000000 : ℝ)|^67 ≤ (3026916383283/50000000000000 : ℝ)^51
        have hw : |(-1182738753/10000000000 : ℝ)|=(1182738753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5217940417/10000000000 : ℝ)|^67 ≤ (42547239427651/100000000000000 : ℝ)^51
        have hw : |(-5217940417/10000000000 : ℝ)|=(5217940417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s3_s3_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (768049647/2500000000 : ℝ)*x 0 + (7551135509/10000000000 : ℝ)*x 1 + (105356207/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (768049647/2500000000 : ℝ)^67 ≤ (21215294312809/100000000000000 : ℝ)^51 := by
    have hnat : (768049647 : ℕ)^67*100000000000000^51 ≤ 21215294312809^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768049647 2500000000 21215294312809 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7551135509/10000000000 : ℝ)^67 ≤ (3457097324651/5000000000000 : ℝ)^51 := by
    have hnat : (7551135509 : ℕ)^67*5000000000000^51 ≤ 3457097324651^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7551135509 10000000000 3457097324651 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105356207/625000000 : ℝ)^67 ≤ (4821379586187/50000000000000 : ℝ)^51 := by
    have hnat : (105356207 : ℕ)^67*50000000000000^51 ≤ 4821379586187^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105356207 625000000 4821379586187 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(768049647/2500000000 : ℝ), (7551135509/10000000000 : ℝ), (105356207/625000000 : ℝ)] ![(21215294312809/100000000000000 : ℝ), (3457097324651/5000000000000 : ℝ), (4821379586187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(768049647/2500000000 : ℝ)|^67 ≤ (21215294312809/100000000000000 : ℝ)^51
        have hw : |(768049647/2500000000 : ℝ)|=(768049647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7551135509/10000000000 : ℝ)|^67 ≤ (3457097324651/5000000000000 : ℝ)^51
        have hw : |(7551135509/10000000000 : ℝ)|=(7551135509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105356207/625000000 : ℝ)|^67 ≤ (4821379586187/50000000000000 : ℝ)^51
        have hw : |(105356207/625000000 : ℝ)|=(105356207/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305060_s3_s3_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4437088159/5000000000 : ℝ)*x 0 + (2295788937/10000000000 : ℝ)*x 1 + (-16032869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4437088159/5000000000 : ℝ)^67 ≤ (21369507348989/25000000000000 : ℝ)^51 := by
    have hnat : (4437088159 : ℕ)^67*25000000000000^51 ≤ 21369507348989^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4437088159 5000000000 21369507348989 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2295788937/10000000000 : ℝ)^67 ≤ (1446905022807/10000000000000 : ℝ)^51 := by
    have hnat : (2295788937 : ℕ)^67*10000000000000^51 ≤ 1446905022807^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295788937 10000000000 1446905022807 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16032869/5000000000 : ℝ)^67 ≤ (26460180931/50000000000000 : ℝ)^51 := by
    have hnat : (16032869 : ℕ)^67*50000000000000^51 ≤ 26460180931^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16032869 5000000000 26460180931 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4437088159/5000000000 : ℝ), (2295788937/10000000000 : ℝ), (-16032869/5000000000 : ℝ)] ![(21369507348989/25000000000000 : ℝ), (1446905022807/10000000000000 : ℝ), (26460180931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4437088159/5000000000 : ℝ)|^67 ≤ (21369507348989/25000000000000 : ℝ)^51
        have hw : |(4437088159/5000000000 : ℝ)|=(4437088159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2295788937/10000000000 : ℝ)|^67 ≤ (1446905022807/10000000000000 : ℝ)^51
        have hw : |(2295788937/10000000000 : ℝ)|=(2295788937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16032869/5000000000 : ℝ)|^67 ≤ (26460180931/50000000000000 : ℝ)^51
        have hw : |(-16032869/5000000000 : ℝ)|=(16032869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305060_s3 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((84723/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84723/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1711/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1711/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-75157/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-75157/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((73437/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73437/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75101/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75101/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-61741/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-61741/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (93447/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (84723/100000 : ℝ) ^ (133/32 : ℝ) ≤ (25102993495628830343/50000000000000000000 : ℝ) := by
    have hpowers : (84723/100000 : ℝ)^133 ≤ (25102993495628830343/50000000000000000000 : ℝ)^32 := by
      have hnat : (84723 : ℕ)^133*50000000000000000000^32 ≤ 25102993495628830343^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        84723 100000 25102993495628830343 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (84723/100000 : ℝ)) (X := (25102993495628830343/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (75102993495628830343/50000000000000000000 : ℝ) ≤ (11028367162505513/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (75102993495628830343/50000000000000000000 : ℝ)^32 ≤ (11028367162505513/10000000000000000 : ℝ)^133 := by
      have hnat : (75102993495628830343 : ℕ)^32*10000000000000000^133 ≤ 11028367162505513^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75102993495628830343 50000000000000000000 11028367162505513 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11028367162505513/10000000000000000 : ℝ)) (X := (75102993495628830343/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (50102993495628830343/25000000000000000000 : ℝ) ≤ (5910351259704549/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50102993495628830343/25000000000000000000 : ℝ)^32 ≤ (5910351259704549/5000000000000000 : ℝ)^133 := by
      have hnat : (50102993495628830343 : ℕ)^32*5000000000000000^133 ≤ 5910351259704549^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50102993495628830343 25000000000000000000 5910351259704549 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5910351259704549/5000000000000000 : ℝ)) (X := (50102993495628830343/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1028367162505513/8472300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(158467071380717/1694460000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (84723/100000 : ℝ)) (alpha := (1028367162505513/8472300000000000 : ℝ)) (beta := (158467071380717/1694460000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (84723/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1028367162505513/8472300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(158467071380717/1694460000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (1711/2000 : ℝ) ^ (133/32 : ℝ) ≤ (26137222625513612099/50000000000000000000 : ℝ) := by
    have hpowers : (1711/2000 : ℝ)^133 ≤ (26137222625513612099/50000000000000000000 : ℝ)^32 := by
      have hnat : (1711 : ℕ)^133*50000000000000000000^32 ≤ 26137222625513612099^32*2000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1711 2000 26137222625513612099 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1711/2000 : ℝ)) (X := (26137222625513612099/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (76137222625513612099/50000000000000000000 : ℝ) ≤ (11064717676154641/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (76137222625513612099/50000000000000000000 : ℝ)^32 ≤ (11064717676154641/10000000000000000 : ℝ)^133 := by
      have hnat : (76137222625513612099 : ℕ)^32*10000000000000000^133 ≤ 11064717676154641^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76137222625513612099 50000000000000000000 11064717676154641 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11064717676154641/10000000000000000 : ℝ)) (X := (76137222625513612099/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (51137222625513612099/25000000000000000000 : ℝ) ≤ (5939477763505479/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (51137222625513612099/25000000000000000000 : ℝ)^32 ≤ (5939477763505479/5000000000000000 : ℝ)^133 := by
      have hnat : (51137222625513612099 : ℕ)^32*5000000000000000^133 ≤ 5939477763505479^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51137222625513612099 25000000000000000000 5939477763505479 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5939477763505479/5000000000000000 : ℝ)) (X := (51137222625513612099/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1064717676154641/8555000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(814237850856317/8555000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1711/2000 : ℝ)) (alpha := (1064717676154641/8555000000000000 : ℝ)) (beta := (814237850856317/8555000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1711/2000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1064717676154641/8555000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(814237850856317/8555000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (75157/100000 : ℝ) ^ (133/32 : ℝ) ≤ (3814239703783737513/12500000000000000000 : ℝ) := by
    have hpowers : (75157/100000 : ℝ)^133 ≤ (3814239703783737513/12500000000000000000 : ℝ)^32 := by
      have hnat : (75157 : ℕ)^133*12500000000000000000^32 ≤ 3814239703783737513^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75157 100000 3814239703783737513 12500000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75157/100000 : ℝ)) (X := (3814239703783737513/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (16314239703783737513/12500000000000000000 : ℝ) ≤ (10661718366268371/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (16314239703783737513/12500000000000000000 : ℝ)^32 ≤ (10661718366268371/10000000000000000 : ℝ)^133 := by
      have hnat : (16314239703783737513 : ℕ)^32*10000000000000000^133 ≤ 10661718366268371^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16314239703783737513 12500000000000000000 10661718366268371 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10661718366268371/10000000000000000 : ℝ)) (X := (16314239703783737513/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (10064239703783737513/6250000000000000000 : ℝ) ≤ (5607259884053677/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (10064239703783737513/6250000000000000000 : ℝ)^32 ≤ (5607259884053677/5000000000000000 : ℝ)^133 := by
      have hnat : (10064239703783737513 : ℕ)^32*5000000000000000^133 ≤ 5607259884053677^133*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10064239703783737513 6250000000000000000 5607259884053677 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5607259884053677/5000000000000000 : ℝ)) (X := (10064239703783737513/6250000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(661718366268371/7515700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(552801401838983/7515700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (75157/100000 : ℝ)) (alpha := (661718366268371/7515700000000000 : ℝ)) (beta := (552801401838983/7515700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (75157/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(661718366268371/7515700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(552801401838983/7515700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-936186787/5000000000 : ℝ)*X 0 0+(1107639897/2500000000 : ℝ)*X 0 1+(-3154921987/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((2242865087/5000000000 : ℝ)*X 1 0+(-974940723/5000000000 : ℝ)*X 1 1+(-9930913/16000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-399377501/2000000000 : ℝ)*X 0 0+(2857154983/10000000000 : ℝ)*X 0 1+(-7511655771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((3182539843/10000000000 : ℝ)*X 1 0+(-1592091541/10000000000 : ℝ)*X 1 1+(-752540391/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((3480277069/10000000000 : ℝ)*X 2 0+(7310792993/10000000000 : ℝ)*X 2 1+(782244081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((2575456227/5000000000 : ℝ)*X 0 0+(6620434411/10000000000 : ℝ)*X 0 1+(117/2000000000 : ℝ)*X 0 2+(2575456227/5000000000 : ℝ)*X 1 0+(6620434411/10000000000 : ℝ)*X 1 1+(117/2000000000 : ℝ)*X 1 2+(2575456227/5000000000 : ℝ)*X 2 0+(6620434411/10000000000 : ℝ)*X 2 1+(117/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-188370391/1250000000 : ℝ)*X 0 0+(2920118787/10000000000 : ℝ)*X 0 1+(-7773664467/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((622076071/2500000000 : ℝ)*X 1 0+(-1979978099/10000000000 : ℝ)*X 1 1+(-3893947221/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((791112497/1250000000 : ℝ)*X 2 0+(459505553/1000000000 : ℝ)*X 2 1+(50696177/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((8435923191/10000000000 : ℝ)*X 0 0+(293993269/1000000000 : ℝ)*X 0 1+(-1128111/10000000000 : ℝ)*X 0 2+(8435923191/10000000000 : ℝ)*X 1 0+(293993269/1000000000 : ℝ)*X 1 1+(-1128111/10000000000 : ℝ)*X 1 2+(8435923191/10000000000 : ℝ)*X 2 0+(293993269/1000000000 : ℝ)*X 2 1+(-1128111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-548830631/5000000000 : ℝ)*X 0 0+(5965262403/10000000000 : ℝ)*X 0 1+(-5333065993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((1506329441/2500000000 : ℝ)*X 1 0+(-1182738753/10000000000 : ℝ)*X 1 1+(-5217940417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((768049647/2500000000 : ℝ)*X 2 0+(7551135509/10000000000 : ℝ)*X 2 1+(105356207/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((4437088159/5000000000 : ℝ)*X 0 0+(2295788937/10000000000 : ℝ)*X 0 1+(-16032869/5000000000 : ℝ)*X 0 2+(4437088159/5000000000 : ℝ)*X 1 0+(2295788937/10000000000 : ℝ)*X 1 1+(-16032869/5000000000 : ℝ)*X 1 2+(4437088159/5000000000 : ℝ)*X 2 0+(2295788937/10000000000 : ℝ)*X 2 1+(-16032869/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305060_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((73437/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73437/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3979106951181865123724391/221713150000000000000000000000 : ℝ) := by norm_num
    linear_combination (2290572169/500000000000 : ℝ)*(base5) + (6629868317/10000000000 : ℝ)*(base7) + (1416359/1000000000000 : ℝ)*(base59) + (14590882897/5000000000 : ℝ)*(major_s3_0) + (14590882897/5000000000 : ℝ)*(major_s3_1) + (14590882897/5000000000 : ℝ)*(major_s3_2) + (28577959/1000000000000 : ℝ)*(sp_s3_0) + (538051/62500000000 : ℝ)*(sp_s3_1) + (878746526251/250000000000 : ℝ)*(sp_s3_7) + (3515082567559/1000000000000 : ℝ)*(sp_s3_8) + (439962231581/125000000000 : ℝ)*(sp_s3_9) + (641652154767/250000000000 : ℝ)*(sp_s3_13) + (51012673/500000000000 : ℝ)*(sp_s3_14) + (5106387/200000000000 : ℝ)*(sp_s3_15) + (954101465853/500000000000 : ℝ)*(f.failure) + (351511670831/100000000000 : ℝ)*(f.sum) + (4192559120756743/13857071875000000000000000000 : ℝ)*base62 + (145730596301681/375785000000000000000000000 : ℝ)*base65 + (603501637499/1475000000000000000000000 : ℝ)*base66 + (204716465151641/751570000000000000000000000 : ℝ)*base68 + (3081678422829890693/15918816277500000000000000000000 : ℝ)*base71 + (2845493282413/10590375000000000000000000 : ℝ)*base73 + (272767886227/1475000000000000000000000 : ℝ)*base74 + (3737042951479/13237968750000000000000000 : ℝ)*base76 + (1621890021402917/124966425000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1013/1562500000000000 : ℝ)*base86 + (1013/1562500000000000 : ℝ)*base88 + (1013/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75101/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75101/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (124729470856195721366217678606759/9079031550267500000000000000000000000 : ℝ) := by norm_num
    linear_combination (142526922449/200000000000 : ℝ)*(base7) + (1133/10000000000 : ℝ)*(base39) + (7293559/1000000000000 : ℝ)*(base53) + (2435674754359/1000000000000 : ℝ)*(major_s3_0) + (2435674754359/1000000000000 : ℝ)*(major_s3_1) + (1522292163/625000000 : ℝ)*(major_s3_2) + (16755109/1000000000000 : ℝ)*(sp_s3_0) + (4430893/40000000000 : ℝ)*(sp_s3_8) + (2834668247253/1000000000000 : ℝ)*(sp_s3_14) + (1417287982919/500000000000 : ℝ)*(sp_s3_15) + (1417347015861/500000000000 : ℝ)*(sp_s3_16) + (230529889397/100000000000 : ℝ)*(sp_s3_20) + (8679/5000000000 : ℝ)*(sp_s3_21) + (29505129/1000000000000 : ℝ)*(sp_s3_27) + (796346893427/500000000000 : ℝ)*(f.failure) + (1417347015861/500000000000 : ℝ)*(f.sum) + (447161920618504123317/642968135000000000000000000000000 : ℝ)*base62 + (26235221518467/46973125000000000000000000 : ℝ)*base64 + (307387341674697/8555000000000000000000000000 : ℝ)*base66 + (976170942245983/751570000000000000000000000 : ℝ)*base68 + (65788769512616891441/636752651100000000000000000000000 : ℝ)*base70 + (1961505280449431/1694460000000000000000000000 : ℝ)*base73 + (12169411672371881/8555000000000000000000000000 : ℝ)*base74 + (7950817633031423/8472300000000000000000000000 : ℝ)*base76 + (192488714817068966819/724805265000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (3391/3125000000000000 : ℝ)*base87 + (3391/3125000000000000 : ℝ)*base89 + (3391/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-61741/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-61741/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6523200879123155868920145832623/1134878943783437500000000000000000000 : ℝ) := by norm_num
    linear_combination (117468022483/250000000000 : ℝ)*(base7) + (39574105107/1000000000000 : ℝ)*(base39) + (2688191/200000000000 : ℝ)*(base43) + (2503750145361/1000000000000 : ℝ)*(major_s3_0) + (1251868352203/500000000000 : ℝ)*(major_s3_1) + (2503750145361/1000000000000 : ℝ)*(major_s3_2) + (186061/15625000000 : ℝ)*(sp_s3_0) + (13464429/62500000000 : ℝ)*(sp_s3_9) + (16889573/1000000000000 : ℝ)*(sp_s3_14) + (27372759/1000000000000 : ℝ)*(sp_s3_20) + (192345422949/62500000000 : ℝ)*(sp_s3_21) + (192348062851/62500000000 : ℝ)*(sp_s3_22) + (3077340133797/1000000000000 : ℝ)*(sp_s3_23) + (421410634343/200000000000 : ℝ)*(sp_s3_27) + (818604227271/500000000000 : ℝ)*(f.failure) + (192348062851/62500000000 : ℝ)*(f.sum) + (64847449913301464207/160742033750000000000000000000000 : ℝ)*base62 + (532970074220263/7515700000000000000000000000 : ℝ)*base64 + (87844866790851/4277500000000000000000000000 : ℝ)*base67 + (2379274581854979/7515700000000000000000000000 : ℝ)*base68 + (14750986396361650253/106125441850000000000000000000000 : ℝ)*base70 + (52288656498541/564820000000000000000000000 : ℝ)*base73 + (1953720068026127/4277500000000000000000000000 : ℝ)*base74 + (88300878827169/2824100000000000000000000000 : ℝ)*base76 + (6370347471269824483/60400438750000000000000000000000 : ℝ)*base79 + (3093/3125000000000000 : ℝ)*base87 + (3093/3125000000000000 : ℝ)*base89 + (3093/3125000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((84723/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84723/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1711/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1711/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-75157/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-75157/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((73437/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73437/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75101/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75101/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-61741/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-61741/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305060_s3 p hpa hpb X hX hprev2

#print axioms solution

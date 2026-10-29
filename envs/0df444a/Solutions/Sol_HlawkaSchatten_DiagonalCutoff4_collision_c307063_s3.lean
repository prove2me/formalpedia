-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307063_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:16:21.956843+00:00
-- url     : https://prove2.me/submissions/a29cb7f8-25ef-4b7a-9d9a-39c244364876

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
theorem collision_support_c307063_s3_s3_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-225181759/2500000000 : ℝ)*x 0 + (112142213/200000000 : ℝ)*x 1 + (2887695659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225181759/2500000000 : ℝ)^17 ≤ (4294667714803/100000000000000 : ℝ)^13 := by
    have hnat : (225181759 : ℕ)^17*100000000000000^13 ≤ 4294667714803^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225181759 2500000000 4294667714803 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112142213/200000000 : ℝ)^17 ≤ (11731893102491/25000000000000 : ℝ)^13 := by
    have hnat : (112142213 : ℕ)^17*25000000000000^13 ≤ 11731893102491^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112142213 200000000 11731893102491 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2887695659/5000000000 : ℝ)^17 ≤ (48777759857661/100000000000000 : ℝ)^13 := by
    have hnat : (2887695659 : ℕ)^17*100000000000000^13 ≤ 48777759857661^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2887695659 5000000000 48777759857661 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-225181759/2500000000 : ℝ), (112142213/200000000 : ℝ), (2887695659/5000000000 : ℝ)] ![(4294667714803/100000000000000 : ℝ), (11731893102491/25000000000000 : ℝ), (48777759857661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-225181759/2500000000 : ℝ)|^17 ≤ (4294667714803/100000000000000 : ℝ)^13
        have hw : |(-225181759/2500000000 : ℝ)|=(225181759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112142213/200000000 : ℝ)|^17 ≤ (11731893102491/25000000000000 : ℝ)^13
        have hw : |(112142213/200000000 : ℝ)|=(112142213/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2887695659/5000000000 : ℝ)|^17 ≤ (48777759857661/100000000000000 : ℝ)^13
        have hw : |(2887695659/5000000000 : ℝ)|=(2887695659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s3_s3_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (35046023/62500000 : ℝ)*x 0 + (-90526037/1000000000 : ℝ)*x 1 + (5772579133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35046023/62500000 : ℝ)^17 ≤ (11732585426783/25000000000000 : ℝ)^13 := by
    have hnat : (35046023 : ℕ)^17*25000000000000^13 ≤ 11732585426783^13*62500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35046023 62500000 11732585426783 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90526037/1000000000 : ℝ)^17 ≤ (4322955269813/100000000000000 : ℝ)^13 := by
    have hnat : (90526037 : ℕ)^17*100000000000000^13 ≤ 4322955269813^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90526037 1000000000 4322955269813 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5772579133/10000000000 : ℝ)^17 ≤ (24373351505653/50000000000000 : ℝ)^13 := by
    have hnat : (5772579133 : ℕ)^17*50000000000000^13 ≤ 24373351505653^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5772579133 10000000000 24373351505653 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(35046023/62500000 : ℝ), (-90526037/1000000000 : ℝ), (5772579133/10000000000 : ℝ)] ![(11732585426783/25000000000000 : ℝ), (4322955269813/100000000000000 : ℝ), (24373351505653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(35046023/62500000 : ℝ)|^17 ≤ (11732585426783/25000000000000 : ℝ)^13
        have hw : |(35046023/62500000 : ℝ)|=(35046023/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90526037/1000000000 : ℝ)|^17 ≤ (4322955269813/100000000000000 : ℝ)^13
        have hw : |(-90526037/1000000000 : ℝ)|=(90526037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5772579133/10000000000 : ℝ)|^17 ≤ (24373351505653/50000000000000 : ℝ)^13
        have hw : |(5772579133/10000000000 : ℝ)|=(5772579133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s3_s3_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (226799919/400000000 : ℝ)*x 0 + (287389117/500000000 : ℝ)*x 1 + (-26198253/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (226799919/400000000 : ℝ)^17 ≤ (9523405012787/20000000000000 : ℝ)^13 := by
    have hnat : (226799919 : ℕ)^17*20000000000000^13 ≤ 9523405012787^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226799919 400000000 9523405012787 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287389117/500000000 : ℝ)^17 ≤ (48473057046607/100000000000000 : ℝ)^13 := by
    have hnat : (287389117 : ℕ)^17*100000000000000^13 ≤ 48473057046607^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287389117 500000000 48473057046607 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26198253/312500000 : ℝ)^17 ≤ (3909917883497/100000000000000 : ℝ)^13 := by
    have hnat : (26198253 : ℕ)^17*100000000000000^13 ≤ 3909917883497^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26198253 312500000 3909917883497 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(226799919/400000000 : ℝ), (287389117/500000000 : ℝ), (-26198253/312500000 : ℝ)] ![(9523405012787/20000000000000 : ℝ), (48473057046607/100000000000000 : ℝ), (3909917883497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(226799919/400000000 : ℝ)|^17 ≤ (9523405012787/20000000000000 : ℝ)^13
        have hw : |(226799919/400000000 : ℝ)|=(226799919/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(287389117/500000000 : ℝ)|^17 ≤ (48473057046607/100000000000000 : ℝ)^13
        have hw : |(287389117/500000000 : ℝ)|=(287389117/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26198253/312500000 : ℝ)|^17 ≤ (3909917883497/100000000000000 : ℝ)^13
        have hw : |(-26198253/312500000 : ℝ)|=(26198253/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s3_s3_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (452642423/1000000000 : ℝ)*x 0 + (108685439/250000000 : ℝ)*x 1 + (2036119317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (452642423/1000000000 : ℝ)^17 ≤ (7093552552301/20000000000000 : ℝ)^13 := by
    have hnat : (452642423 : ℕ)^17*20000000000000^13 ≤ 7093552552301^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452642423 1000000000 7093552552301 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108685439/250000000 : ℝ)^17 ≤ (8411199517237/25000000000000 : ℝ)^13 := by
    have hnat : (108685439 : ℕ)^17*25000000000000^13 ≤ 8411199517237^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108685439 250000000 8411199517237 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2036119317/5000000000 : ℝ)^17 ≤ (6177487830181/20000000000000 : ℝ)^13 := by
    have hnat : (2036119317 : ℕ)^17*20000000000000^13 ≤ 6177487830181^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036119317 5000000000 6177487830181 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(452642423/1000000000 : ℝ), (108685439/250000000 : ℝ), (2036119317/5000000000 : ℝ)] ![(7093552552301/20000000000000 : ℝ), (8411199517237/25000000000000 : ℝ), (6177487830181/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(452642423/1000000000 : ℝ)|^17 ≤ (7093552552301/20000000000000 : ℝ)^13
        have hw : |(452642423/1000000000 : ℝ)|=(452642423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108685439/250000000 : ℝ)|^17 ≤ (8411199517237/25000000000000 : ℝ)^13
        have hw : |(108685439/250000000 : ℝ)|=(108685439/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2036119317/5000000000 : ℝ)|^17 ≤ (6177487830181/20000000000000 : ℝ)^13
        have hw : |(2036119317/5000000000 : ℝ)|=(2036119317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s3_s3_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-120898743/1250000000 : ℝ)*x 0 + (3712442161/10000000000 : ℝ)*x 1 + (7439059613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (120898743/1250000000 : ℝ)^17 ≤ (2356847882929/50000000000000 : ℝ)^13 := by
    have hnat : (120898743 : ℕ)^17*50000000000000^13 ≤ 2356847882929^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120898743 1250000000 2356847882929 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3712442161/10000000000 : ℝ)^17 ≤ (85525833763/312500000000 : ℝ)^13 := by
    have hnat : (3712442161 : ℕ)^17*312500000000^13 ≤ 85525833763^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3712442161 10000000000 85525833763 312500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7439059613/10000000000 : ℝ)^17 ≤ (16979509352653/25000000000000 : ℝ)^13 := by
    have hnat : (7439059613 : ℕ)^17*25000000000000^13 ≤ 16979509352653^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7439059613 10000000000 16979509352653 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-120898743/1250000000 : ℝ), (3712442161/10000000000 : ℝ), (7439059613/10000000000 : ℝ)] ![(2356847882929/50000000000000 : ℝ), (85525833763/312500000000 : ℝ), (16979509352653/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-120898743/1250000000 : ℝ)|^17 ≤ (2356847882929/50000000000000 : ℝ)^13
        have hw : |(-120898743/1250000000 : ℝ)|=(120898743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3712442161/10000000000 : ℝ)|^17 ≤ (85525833763/312500000000 : ℝ)^13
        have hw : |(3712442161/10000000000 : ℝ)|=(3712442161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7439059613/10000000000 : ℝ)|^17 ≤ (16979509352653/25000000000000 : ℝ)^13
        have hw : |(7439059613/10000000000 : ℝ)|=(7439059613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s3_s3_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4142558349/10000000000 : ℝ)*x 0 + (-182711229/10000000000 : ℝ)*x 1 + (1858968251/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4142558349/10000000000 : ℝ)^17 ≤ (6317352822497/20000000000000 : ℝ)^13 := by
    have hnat : (4142558349 : ℕ)^17*20000000000000^13 ≤ 6317352822497^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142558349 10000000000 6317352822497 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182711229/10000000000 : ℝ)^17 ≤ (10664825887/2000000000000 : ℝ)^13 := by
    have hnat : (182711229 : ℕ)^17*2000000000000^13 ≤ 10664825887^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182711229 10000000000 10664825887 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1858968251/2500000000 : ℝ)^17 ≤ (67879994581029/100000000000000 : ℝ)^13 := by
    have hnat : (1858968251 : ℕ)^17*100000000000000^13 ≤ 67879994581029^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858968251 2500000000 67879994581029 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4142558349/10000000000 : ℝ), (-182711229/10000000000 : ℝ), (1858968251/2500000000 : ℝ)] ![(6317352822497/20000000000000 : ℝ), (10664825887/2000000000000 : ℝ), (67879994581029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4142558349/10000000000 : ℝ)|^17 ≤ (6317352822497/20000000000000 : ℝ)^13
        have hw : |(4142558349/10000000000 : ℝ)|=(4142558349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-182711229/10000000000 : ℝ)|^17 ≤ (10664825887/2000000000000 : ℝ)^13
        have hw : |(-182711229/10000000000 : ℝ)|=(182711229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1858968251/2500000000 : ℝ)|^17 ≤ (67879994581029/100000000000000 : ℝ)^13
        have hw : |(1858968251/2500000000 : ℝ)|=(1858968251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s3_s3_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (121439699/312500000 : ℝ)*x 0 + (7682377933/10000000000 : ℝ)*x 1 + (-13510791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121439699/312500000 : ℝ)^17 ≤ (14527010572201/50000000000000 : ℝ)^13 := by
    have hnat : (121439699 : ℕ)^17*50000000000000^13 ≤ 14527010572201^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121439699 312500000 14527010572201 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7682377933/10000000000 : ℝ)^17 ≤ (14167511114163/20000000000000 : ℝ)^13 := by
    have hnat : (7682377933 : ℕ)^17*20000000000000^13 ≤ 14167511114163^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7682377933 10000000000 14167511114163 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13510791/2500000000 : ℝ)^17 ≤ (108423280101/100000000000000 : ℝ)^13 := by
    have hnat : (13510791 : ℕ)^17*100000000000000^13 ≤ 108423280101^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13510791 2500000000 108423280101 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(121439699/312500000 : ℝ), (7682377933/10000000000 : ℝ), (-13510791/2500000000 : ℝ)] ![(14527010572201/50000000000000 : ℝ), (14167511114163/20000000000000 : ℝ), (108423280101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(121439699/312500000 : ℝ)|^17 ≤ (14527010572201/50000000000000 : ℝ)^13
        have hw : |(121439699/312500000 : ℝ)|=(121439699/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7682377933/10000000000 : ℝ)|^17 ≤ (14167511114163/20000000000000 : ℝ)^13
        have hw : |(7682377933/10000000000 : ℝ)|=(7682377933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13510791/2500000000 : ℝ)|^17 ≤ (108423280101/100000000000000 : ℝ)^13
        have hw : |(-13510791/2500000000 : ℝ)|=(13510791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s3_s3_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1947340733/5000000000 : ℝ)*x 0 + (13244343/19531250 : ℝ)*x 1 + (904530391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1947340733/5000000000 : ℝ)^17 ≤ (7284559917859/25000000000000 : ℝ)^13 := by
    have hnat : (1947340733 : ℕ)^17*25000000000000^13 ≤ 7284559917859^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947340733 5000000000 7284559917859 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13244343/19531250 : ℝ)^17 ≤ (7521471569851/12500000000000 : ℝ)^13 := by
    have hnat : (13244343 : ℕ)^17*12500000000000^13 ≤ 7521471569851^13*19531250^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13244343 19531250 7521471569851 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904530391/5000000000 : ℝ)^17 ≤ (1068998775349/10000000000000 : ℝ)^13 := by
    have hnat : (904530391 : ℕ)^17*10000000000000^13 ≤ 1068998775349^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904530391 5000000000 1068998775349 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1947340733/5000000000 : ℝ), (13244343/19531250 : ℝ), (904530391/5000000000 : ℝ)] ![(7284559917859/25000000000000 : ℝ), (7521471569851/12500000000000 : ℝ), (1068998775349/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1947340733/5000000000 : ℝ)|^17 ≤ (7284559917859/25000000000000 : ℝ)^13
        have hw : |(1947340733/5000000000 : ℝ)|=(1947340733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13244343/19531250 : ℝ)|^17 ≤ (7521471569851/12500000000000 : ℝ)^13
        have hw : |(13244343/19531250 : ℝ)|=(13244343/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(904530391/5000000000 : ℝ)|^17 ≤ (1068998775349/10000000000000 : ℝ)^13
        have hw : |(904530391/5000000000 : ℝ)|=(904530391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s3_s3_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-151232143/10000000000 : ℝ)*x 0 + (4061864363/10000000000 : ℝ)*x 1 + (7512735181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (151232143/10000000000 : ℝ)^17 ≤ (104105724093/25000000000000 : ℝ)^13 := by
    have hnat : (151232143 : ℕ)^17*25000000000000^13 ≤ 104105724093^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151232143 10000000000 104105724093 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4061864363/10000000000 : ℝ)^17 ≤ (3078458034149/10000000000000 : ℝ)^13 := by
    have hnat : (4061864363 : ℕ)^17*10000000000000^13 ≤ 3078458034149^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4061864363 10000000000 3078458034149 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7512735181/10000000000 : ℝ)^17 ≤ (68798996755121/100000000000000 : ℝ)^13 := by
    have hnat : (7512735181 : ℕ)^17*100000000000000^13 ≤ 68798996755121^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7512735181 10000000000 68798996755121 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-151232143/10000000000 : ℝ), (4061864363/10000000000 : ℝ), (7512735181/10000000000 : ℝ)] ![(104105724093/25000000000000 : ℝ), (3078458034149/10000000000000 : ℝ), (68798996755121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-151232143/10000000000 : ℝ)|^17 ≤ (104105724093/25000000000000 : ℝ)^13
        have hw : |(-151232143/10000000000 : ℝ)|=(151232143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4061864363/10000000000 : ℝ)|^17 ≤ (3078458034149/10000000000000 : ℝ)^13
        have hw : |(4061864363/10000000000 : ℝ)|=(4061864363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7512735181/10000000000 : ℝ)|^17 ≤ (68798996755121/100000000000000 : ℝ)^13
        have hw : |(7512735181/10000000000 : ℝ)|=(7512735181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s3_s3_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (903503863/2500000000 : ℝ)*x 0 + (-98326531/1000000000 : ℝ)*x 1 + (3754751801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (903503863/2500000000 : ℝ)^17 ≤ (26423292341513/100000000000000 : ℝ)^13 := by
    have hnat : (903503863 : ℕ)^17*100000000000000^13 ≤ 26423292341513^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903503863 2500000000 26423292341513 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98326531/1000000000 : ℝ)^17 ≤ (2408203870687/50000000000000 : ℝ)^13 := by
    have hnat : (98326531 : ℕ)^17*50000000000000^13 ≤ 2408203870687^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98326531 1000000000 2408203870687 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3754751801/5000000000 : ℝ)^17 ≤ (8595037487993/12500000000000 : ℝ)^13 := by
    have hnat : (3754751801 : ℕ)^17*12500000000000^13 ≤ 8595037487993^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3754751801 5000000000 8595037487993 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(903503863/2500000000 : ℝ), (-98326531/1000000000 : ℝ), (3754751801/5000000000 : ℝ)] ![(26423292341513/100000000000000 : ℝ), (2408203870687/50000000000000 : ℝ), (8595037487993/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(903503863/2500000000 : ℝ)|^17 ≤ (26423292341513/100000000000000 : ℝ)^13
        have hw : |(903503863/2500000000 : ℝ)|=(903503863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98326531/1000000000 : ℝ)|^17 ≤ (2408203870687/50000000000000 : ℝ)^13
        have hw : |(-98326531/1000000000 : ℝ)|=(98326531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3754751801/5000000000 : ℝ)|^17 ≤ (8595037487993/12500000000000 : ℝ)^13
        have hw : |(3754751801/5000000000 : ℝ)|=(3754751801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s3_s3_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3698238337/5000000000 : ℝ)*x 0 + (1055862757/2500000000 : ℝ)*x 1 + (-42189019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3698238337/5000000000 : ℝ)^17 ≤ (6741008251223/10000000000000 : ℝ)^13 := by
    have hnat : (3698238337 : ℕ)^17*10000000000000^13 ≤ 6741008251223^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3698238337 5000000000 6741008251223 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055862757/2500000000 : ℝ)^17 ≤ (1295830542281/4000000000000 : ℝ)^13 := by
    have hnat : (1055862757 : ℕ)^17*4000000000000^13 ≤ 1295830542281^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055862757 2500000000 1295830542281 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42189019/5000000000 : ℝ)^17 ≤ (4853848053/2500000000000 : ℝ)^13 := by
    have hnat : (42189019 : ℕ)^17*2500000000000^13 ≤ 4853848053^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42189019 5000000000 4853848053 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3698238337/5000000000 : ℝ), (1055862757/2500000000 : ℝ), (-42189019/5000000000 : ℝ)] ![(6741008251223/10000000000000 : ℝ), (1295830542281/4000000000000 : ℝ), (4853848053/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3698238337/5000000000 : ℝ)|^17 ≤ (6741008251223/10000000000000 : ℝ)^13
        have hw : |(3698238337/5000000000 : ℝ)|=(3698238337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055862757/2500000000 : ℝ)|^17 ≤ (1295830542281/4000000000000 : ℝ)^13
        have hw : |(1055862757/2500000000 : ℝ)|=(1055862757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42189019/5000000000 : ℝ)|^17 ≤ (4853848053/2500000000000 : ℝ)^13
        have hw : |(-42189019/5000000000 : ℝ)|=(42189019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s3_s3_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3690853907/5000000000 : ℝ)*x 0 + (1581548627/5000000000 : ℝ)*x 1 + (1793322397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3690853907/5000000000 : ℝ)^17 ≤ (33617060230497/50000000000000 : ℝ)^13 := by
    have hnat : (3690853907 : ℕ)^17*50000000000000^13 ≤ 33617060230497^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3690853907 5000000000 33617060230497 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1581548627/5000000000 : ℝ)^17 ≤ (22197344411529/100000000000000 : ℝ)^13 := by
    have hnat : (1581548627 : ℕ)^17*100000000000000^13 ≤ 22197344411529^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1581548627 5000000000 22197344411529 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1793322397/10000000000 : ℝ)^17 ≤ (10568535115939/100000000000000 : ℝ)^13 := by
    have hnat : (1793322397 : ℕ)^17*100000000000000^13 ≤ 10568535115939^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793322397 10000000000 10568535115939 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3690853907/5000000000 : ℝ), (1581548627/5000000000 : ℝ), (1793322397/10000000000 : ℝ)] ![(33617060230497/50000000000000 : ℝ), (22197344411529/100000000000000 : ℝ), (10568535115939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3690853907/5000000000 : ℝ)|^17 ≤ (33617060230497/50000000000000 : ℝ)^13
        have hw : |(3690853907/5000000000 : ℝ)|=(3690853907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1581548627/5000000000 : ℝ)|^17 ≤ (22197344411529/100000000000000 : ℝ)^13
        have hw : |(1581548627/5000000000 : ℝ)|=(1581548627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1793322397/10000000000 : ℝ)|^17 ≤ (10568535115939/100000000000000 : ℝ)^13
        have hw : |(1793322397/10000000000 : ℝ)|=(1793322397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s3_s3_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-6202473/500000000 : ℝ)*x 0 + (859999337/1250000000 : ℝ)*x 1 + (300359711/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6202473/500000000 : ℝ)^17 ≤ (80343120467/25000000000000 : ℝ)^13 := by
    have hnat : (6202473 : ℕ)^17*25000000000000^13 ≤ 80343120467^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6202473 500000000 80343120467 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (859999337/1250000000 : ℝ)^17 ≤ (61321844873677/100000000000000 : ℝ)^13 := by
    have hnat : (859999337 : ℕ)^17*100000000000000^13 ≤ 61321844873677^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859999337 1250000000 61321844873677 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300359711/625000000 : ℝ)^17 ≤ (38356782628029/100000000000000 : ℝ)^13 := by
    have hnat : (300359711 : ℕ)^17*100000000000000^13 ≤ 38356782628029^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300359711 625000000 38356782628029 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6202473/500000000 : ℝ), (859999337/1250000000 : ℝ), (300359711/625000000 : ℝ)] ![(80343120467/25000000000000 : ℝ), (61321844873677/100000000000000 : ℝ), (38356782628029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6202473/500000000 : ℝ)|^17 ≤ (80343120467/25000000000000 : ℝ)^13
        have hw : |(-6202473/500000000 : ℝ)|=(6202473/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(859999337/1250000000 : ℝ)|^17 ≤ (61321844873677/100000000000000 : ℝ)^13
        have hw : |(859999337/1250000000 : ℝ)|=(859999337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(300359711/625000000 : ℝ)|^17 ≤ (38356782628029/100000000000000 : ℝ)^13
        have hw : |(300359711/625000000 : ℝ)|=(300359711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s3_s3_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (230297281/312500000 : ℝ)*x 0 + (-37178661/5000000000 : ℝ)*x 1 + (2129187857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230297281/312500000 : ℝ)^17 ≤ (16772227034259/25000000000000 : ℝ)^13 := by
    have hnat : (230297281 : ℕ)^17*25000000000000^13 ≤ 16772227034259^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230297281 312500000 16772227034259 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37178661/5000000000 : ℝ)^17 ≤ (164568393423/100000000000000 : ℝ)^13 := by
    have hnat : (37178661 : ℕ)^17*100000000000000^13 ≤ 164568393423^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37178661 5000000000 164568393423 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2129187857/5000000000 : ℝ)^17 ≤ (8186630864999/25000000000000 : ℝ)^13 := by
    have hnat : (2129187857 : ℕ)^17*25000000000000^13 ≤ 8186630864999^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129187857 5000000000 8186630864999 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(230297281/312500000 : ℝ), (-37178661/5000000000 : ℝ), (2129187857/5000000000 : ℝ)] ![(16772227034259/25000000000000 : ℝ), (164568393423/100000000000000 : ℝ), (8186630864999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(230297281/312500000 : ℝ)|^17 ≤ (16772227034259/25000000000000 : ℝ)^13
        have hw : |(230297281/312500000 : ℝ)|=(230297281/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37178661/5000000000 : ℝ)|^17 ≤ (164568393423/100000000000000 : ℝ)^13
        have hw : |(-37178661/5000000000 : ℝ)|=(37178661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2129187857/5000000000 : ℝ)|^17 ≤ (8186630864999/25000000000000 : ℝ)^13
        have hw : |(2129187857/5000000000 : ℝ)|=(2129187857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s3_s3_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (445730289/1250000000 : ℝ)*x 0 + (60688859/80000000 : ℝ)*x 1 + (-910765959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (445730289/1250000000 : ℝ)^17 ≤ (25963657261633/100000000000000 : ℝ)^13 := by
    have hnat : (445730289 : ℕ)^17*100000000000000^13 ≤ 25963657261633^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445730289 1250000000 25963657261633 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60688859/80000000 : ℝ)^17 ≤ (13935794897763/20000000000000 : ℝ)^13 := by
    have hnat : (60688859 : ℕ)^17*20000000000000^13 ≤ 13935794897763^13*80000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60688859 80000000 13935794897763 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (910765959/10000000000 : ℝ)^17 ≤ (4357368241933/100000000000000 : ℝ)^13 := by
    have hnat : (910765959 : ℕ)^17*100000000000000^13 ≤ 4357368241933^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910765959 10000000000 4357368241933 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(445730289/1250000000 : ℝ), (60688859/80000000 : ℝ), (-910765959/10000000000 : ℝ)] ![(25963657261633/100000000000000 : ℝ), (13935794897763/20000000000000 : ℝ), (4357368241933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(445730289/1250000000 : ℝ)|^17 ≤ (25963657261633/100000000000000 : ℝ)^13
        have hw : |(445730289/1250000000 : ℝ)|=(445730289/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(60688859/80000000 : ℝ)|^17 ≤ (13935794897763/20000000000000 : ℝ)^13
        have hw : |(60688859/80000000 : ℝ)|=(60688859/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-910765959/10000000000 : ℝ)|^17 ≤ (4357368241933/100000000000000 : ℝ)^13
        have hw : |(-910765959/10000000000 : ℝ)|=(910765959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s3_s3_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7522843529/10000000000 : ℝ)*x 0 + (262993691/1000000000 : ℝ)*x 1 + (54500867/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7522843529/10000000000 : ℝ)^17 ≤ (17230018298591/25000000000000 : ℝ)^13 := by
    have hnat : (7522843529 : ℕ)^17*25000000000000^13 ≤ 17230018298591^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7522843529 10000000000 17230018298591 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262993691/1000000000 : ℝ)^17 ≤ (8718403695871/50000000000000 : ℝ)^13 := by
    have hnat : (262993691 : ℕ)^17*50000000000000^13 ≤ 8718403695871^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262993691 1000000000 8718403695871 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54500867/250000000 : ℝ)^17 ≤ (136431194043/1000000000000 : ℝ)^13 := by
    have hnat : (54500867 : ℕ)^17*1000000000000^13 ≤ 136431194043^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54500867 250000000 136431194043 1000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7522843529/10000000000 : ℝ), (262993691/1000000000 : ℝ), (54500867/250000000 : ℝ)] ![(17230018298591/25000000000000 : ℝ), (8718403695871/50000000000000 : ℝ), (136431194043/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7522843529/10000000000 : ℝ)|^17 ≤ (17230018298591/25000000000000 : ℝ)^13
        have hw : |(7522843529/10000000000 : ℝ)|=(7522843529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262993691/1000000000 : ℝ)|^17 ≤ (8718403695871/50000000000000 : ℝ)^13
        have hw : |(262993691/1000000000 : ℝ)|=(262993691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54500867/250000000 : ℝ)|^17 ≤ (136431194043/1000000000000 : ℝ)^13
        have hw : |(54500867/250000000 : ℝ)|=(54500867/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307063_s3 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((9429/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9429/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37809/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37809/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2276/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2276/3125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6499/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6499/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1641/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1641/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15757/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15757/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92559/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (9429/12500 : ℝ) ^ (135/32 : ℝ) ≤ (7609879712888958789/25000000000000000000 : ℝ) := by
    have hpowers : (9429/12500 : ℝ)^135 ≤ (7609879712888958789/25000000000000000000 : ℝ)^32 := by
      have hnat : (9429 : ℕ)^135*25000000000000000000^32 ≤ 7609879712888958789^32*12500^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9429 12500 7609879712888958789 25000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9429/12500 : ℝ)) (X := (7609879712888958789/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (32609879712888958789/25000000000000000000 : ℝ) ≤ (5325081467357253/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (32609879712888958789/25000000000000000000 : ℝ)^32 ≤ (5325081467357253/5000000000000000 : ℝ)^135 := by
      have hnat : (32609879712888958789 : ℕ)^32*5000000000000000^135 ≤ 5325081467357253^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32609879712888958789 25000000000000000000 5325081467357253 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5325081467357253/5000000000000000 : ℝ)) (X := (32609879712888958789/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (20109879712888958789/12500000000000000000 : ℝ) ≤ (11193039080863983/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (20109879712888958789/12500000000000000000 : ℝ)^32 ≤ (11193039080863983/10000000000000000 : ℝ)^135 := by
      have hnat : (20109879712888958789 : ℕ)^32*10000000000000000^135 ≤ 11193039080863983^135*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20109879712888958789 12500000000000000000 11193039080863983 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11193039080863983/10000000000000000 : ℝ)) (X := (20109879712888958789/12500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(325081467357253/3771600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(25851245054737/359200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (9429/12500 : ℝ)) (alpha := (325081467357253/3771600000000000 : ℝ)) (beta := (25851245054737/359200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (9429/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(325081467357253/3771600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(25851245054737/359200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (37809/50000 : ℝ) ^ (135/32 : ℝ) ≤ (6151485459796779869/20000000000000000000 : ℝ) := by
    have hpowers : (37809/50000 : ℝ)^135 ≤ (6151485459796779869/20000000000000000000 : ℝ)^32 := by
      have hnat : (37809 : ℕ)^135*20000000000000000000^32 ≤ 6151485459796779869^32*50000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37809 50000 6151485459796779869 20000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37809/50000 : ℝ)) (X := (6151485459796779869/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (26151485459796779869/20000000000000000000 : ℝ) ≤ (666019369799067/625000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (26151485459796779869/20000000000000000000 : ℝ)^32 ≤ (666019369799067/625000000000000 : ℝ)^135 := by
      have hnat : (26151485459796779869 : ℕ)^32*625000000000000^135 ≤ 666019369799067^135*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26151485459796779869 20000000000000000000 666019369799067 625000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (666019369799067/625000000000000 : ℝ)) (X := (26151485459796779869/20000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (16151485459796779869/10000000000000000000 : ℝ) ≤ (5601754497091923/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (16151485459796779869/10000000000000000000 : ℝ)^32 ≤ (5601754497091923/5000000000000000 : ℝ)^135 := by
      have hnat : (16151485459796779869 : ℕ)^32*5000000000000000^135 ≤ 5601754497091923^135*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16151485459796779869 10000000000000000000 5601754497091923 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5601754497091923/5000000000000000 : ℝ)) (X := (16151485459796779869/10000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(41019369799067/472612500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(91199846233129/1260300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (37809/50000 : ℝ)) (alpha := (41019369799067/472612500000000 : ℝ)) (beta := (91199846233129/1260300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (37809/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(41019369799067/472612500000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(91199846233129/1260300000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (2276/3125 : ℝ) ^ (135/32 : ℝ) ≤ (13126288268696144489/50000000000000000000 : ℝ) := by
    have hpowers : (2276/3125 : ℝ)^135 ≤ (13126288268696144489/50000000000000000000 : ℝ)^32 := by
      have hnat : (2276 : ℕ)^135*50000000000000000000^32 ≤ 13126288268696144489^32*3125^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2276 3125 13126288268696144489 50000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2276/3125 : ℝ)) (X := (13126288268696144489/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (63126288268696144489/50000000000000000000 : ℝ) ≤ (5284059426355923/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (63126288268696144489/50000000000000000000 : ℝ)^32 ≤ (5284059426355923/5000000000000000 : ℝ)^135 := by
      have hnat : (63126288268696144489 : ℕ)^32*5000000000000000^135 ≤ 5284059426355923^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63126288268696144489 50000000000000000000 5284059426355923 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5284059426355923/5000000000000000 : ℝ)) (X := (63126288268696144489/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (38126288268696144489/25000000000000000000 : ℝ) ≤ (2210422104200707/2000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (38126288268696144489/25000000000000000000 : ℝ)^32 ≤ (2210422104200707/2000000000000000 : ℝ)^135 := by
      have hnat : (38126288268696144489 : ℕ)^32*2000000000000000^135 ≤ 2210422104200707^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38126288268696144489 25000000000000000000 2210422104200707 2000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2210422104200707/2000000000000000 : ℝ)) (X := (38126288268696144489/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(284059426355923/3641600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(483991668291689/7283200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (2276/3125 : ℝ)) (alpha := (284059426355923/3641600000000000 : ℝ)) (beta := (483991668291689/7283200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (2276/3125 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(284059426355923/3641600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(483991668291689/7283200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-225181759/2500000000 : ℝ)*X 0 0+(112142213/200000000 : ℝ)*X 0 1+(2887695659/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((35046023/62500000 : ℝ)*X 1 0+(-90526037/1000000000 : ℝ)*X 1 1+(5772579133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((226799919/400000000 : ℝ)*X 2 0+(287389117/500000000 : ℝ)*X 2 1+(-26198253/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((452642423/1000000000 : ℝ)*X 0 0+(108685439/250000000 : ℝ)*X 0 1+(2036119317/5000000000 : ℝ)*X 0 2+(452642423/1000000000 : ℝ)*X 1 0+(108685439/250000000 : ℝ)*X 1 1+(2036119317/5000000000 : ℝ)*X 1 2+(452642423/1000000000 : ℝ)*X 2 0+(108685439/250000000 : ℝ)*X 2 1+(2036119317/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-120898743/1250000000 : ℝ)*X 0 0+(3712442161/10000000000 : ℝ)*X 0 1+(7439059613/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((4142558349/10000000000 : ℝ)*X 1 0+(-182711229/10000000000 : ℝ)*X 1 1+(1858968251/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((121439699/312500000 : ℝ)*X 2 0+(7682377933/10000000000 : ℝ)*X 2 1+(-13510791/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((1947340733/5000000000 : ℝ)*X 0 0+(13244343/19531250 : ℝ)*X 0 1+(904530391/5000000000 : ℝ)*X 0 2+(1947340733/5000000000 : ℝ)*X 1 0+(13244343/19531250 : ℝ)*X 1 1+(904530391/5000000000 : ℝ)*X 1 2+(1947340733/5000000000 : ℝ)*X 2 0+(13244343/19531250 : ℝ)*X 2 1+(904530391/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-151232143/10000000000 : ℝ)*X 0 0+(4061864363/10000000000 : ℝ)*X 0 1+(7512735181/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((903503863/2500000000 : ℝ)*X 1 0+(-98326531/1000000000 : ℝ)*X 1 1+(3754751801/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((3698238337/5000000000 : ℝ)*X 2 0+(1055862757/2500000000 : ℝ)*X 2 1+(-42189019/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((3690853907/5000000000 : ℝ)*X 0 0+(1581548627/5000000000 : ℝ)*X 0 1+(1793322397/10000000000 : ℝ)*X 0 2+(3690853907/5000000000 : ℝ)*X 1 0+(1581548627/5000000000 : ℝ)*X 1 1+(1793322397/10000000000 : ℝ)*X 1 2+(3690853907/5000000000 : ℝ)*X 2 0+(1581548627/5000000000 : ℝ)*X 2 1+(1793322397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-6202473/500000000 : ℝ)*X 0 0+(859999337/1250000000 : ℝ)*X 0 1+(300359711/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((230297281/312500000 : ℝ)*X 1 0+(-37178661/5000000000 : ℝ)*X 1 1+(2129187857/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((445730289/1250000000 : ℝ)*X 2 0+(60688859/80000000 : ℝ)*X 2 1+(-910765959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((7522843529/10000000000 : ℝ)*X 0 0+(262993691/1000000000 : ℝ)*X 0 1+(54500867/250000000 : ℝ)*X 0 2+(7522843529/10000000000 : ℝ)*X 1 0+(262993691/1000000000 : ℝ)*X 1 1+(54500867/250000000 : ℝ)*X 1 2+(7522843529/10000000000 : ℝ)*X 2 0+(262993691/1000000000 : ℝ)*X 2 1+(54500867/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((6499/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6499/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (83976351329422227436252440703/20606893075200000000000000000000000 : ℝ) := by norm_num
    linear_combination (88795803623/200000000000 : ℝ)*(base7) + (209463/500000000000 : ℝ)*(base50) + (3760463111/40000000000 : ℝ)*(base60) + (2318103162329/1000000000000 : ℝ)*(major_s3_0) + (2318103162329/1000000000000 : ℝ)*(major_s3_1) + (2318103162329/1000000000000 : ℝ)*(major_s3_2) + (3855777/1000000000000 : ℝ)*(sp_s3_0) + (6457/5000000000 : ℝ)*(sp_s3_6) + (1435486059171/500000000000 : ℝ)*(sp_s3_7) + (2871003011443/1000000000000 : ℝ)*(sp_s3_8) + (2871001823689/1000000000000 : ℝ)*(sp_s3_9) + (967608994311/500000000000 : ℝ)*(sp_s3_13) + (1081493/40000000000 : ℝ)*(sp_s3_14) + (237551/200000000000 : ℝ)*(sp_s3_23) + (1491240261907/1000000000000 : ℝ)*(f.failure) + (2871003011443/1000000000000 : ℝ)*(f.sum) + (25600365164835652373/137685254400000000000000000000000 : ℝ)*base62 + (815740032275201/7283200000000000000000000000 : ℝ)*base65 + (227532142085389/1260300000000000000000000000 : ℝ)*base66 + (754983222235227/3641600000000000000000000000 : ℝ)*base69 + (1956174395636223409/13734658560000000000000000000000 : ℝ)*base71 + (182173721848553/359200000000000000000000000 : ℝ)*base73 + (4633066057651/236306250000000000000000000 : ℝ)*base74 + (1004053459714003/3771600000000000000000000000 : ℝ)*base76 + (198765106425506411/4526997600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (2417/12500000000000000 : ℝ)*base87 + (2417/12500000000000000 : ℝ)*base89 + (2417/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1641/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1641/2500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (315476081061164340650452279/22947542400000000000000000000000 : ℝ) := by norm_num
    linear_combination (48317630831/100000000000 : ℝ)*(base7) + (1241189/1000000000000 : ℝ)*(base49) + (2206245841891/1000000000000 : ℝ)*(major_s3_0) + (2206245841891/1000000000000 : ℝ)*(major_s3_1) + (2206245841891/1000000000000 : ℝ)*(major_s3_2) + (74781/25000000000 : ℝ)*(sp_s3_1) + (360289/1000000000000 : ℝ)*(sp_s3_2) + (68243751/1000000000000 : ℝ)*(sp_s3_8) + (2695056091799/1000000000000 : ℝ)*(sp_s3_14) + (1347492431383/500000000000 : ℝ)*(sp_s3_15) + (2695055737469/1000000000000 : ℝ)*(sp_s3_16) + (15219140467/8000000000 : ℝ)*(sp_s3_20) + (5959/1000000000000 : ℝ)*(sp_s3_21) + (32990289/500000000000 : ℝ)*(sp_s3_27) + (354820557661/250000000000 : ℝ)*(f.failure) + (2695056097757/1000000000000 : ℝ)*(f.sum) + (83910117322658058953/137685254400000000000000000000000 : ℝ)*base63 + (328653221218021/7283200000000000000000000000 : ℝ)*base64 + (439141081744601/1260300000000000000000000000 : ℝ)*base66 + (3228479284111513/3641600000000000000000000000 : ℝ)*base69 + (79683431687422681/392418816000000000000000000000 : ℝ)*base71 + (158914883309347/359200000000000000000000000 : ℝ)*base73 + (559285585415603/1890450000000000000000000000 : ℝ)*base75 + (16477573786871/538800000000000000000000000 : ℝ)*base76 + (19403433762124151/4526997600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (379/781250000000000 : ℝ)*base87 + (379/781250000000000 : ℝ)*base89 + (379/781250000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15757/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15757/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (241456885793473357720508829661/72124125763200000000000000000000000 : ℝ) := by norm_num
    linear_combination (236816654219/500000000000 : ℝ)*(base7) + (140394348991/1000000000000 : ℝ)*(base40) + (412351/1000000000000 : ℝ)*(base49) + (1058595212617/500000000000 : ℝ)*(major_s3_0) + (1058595212617/500000000000 : ℝ)*(major_s3_1) + (1058595212617/500000000000 : ℝ)*(major_s3_2) + (947167/250000000000 : ℝ)*(sp_s3_1) + (3265521/500000000000 : ℝ)*(sp_s3_2) + (25238687/1000000000000 : ℝ)*(sp_s3_9) + (4245523/500000000000 : ℝ)*(sp_s3_20) + (2580126856903/1000000000000 : ℝ)*(sp_s3_21) + (1290061534117/500000000000 : ℝ)*(sp_s3_22) + (2580095087173/1000000000000 : ℝ)*(sp_s3_23) + (367123505143/200000000000 : ℝ)*(sp_s3_27) + (1361992708323/1000000000000 : ℝ)*(f.failure) + (2580126856903/1000000000000 : ℝ)*(f.sum) + (23465831788421595131/68842627200000000000000000000000 : ℝ)*base63 + (1930571236539407/3641600000000000000000000000 : ℝ)*base64 + (307113564891257/630150000000000000000000000 : ℝ)*base66 + (724445673242731/1820800000000000000000000000 : ℝ)*base69 + (1259597875439016031/6867329280000000000000000000000 : ℝ)*base70 + (47689012636009/179600000000000000000000000 : ℝ)*base73 + (438714545198767/1890450000000000000000000000 : ℝ)*base75 + (181198312865699/1885800000000000000000000000 : ℝ)*base76 + (631818943770514243/2263498800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (787/12500000000000000 : ℝ)*base86 + (787/12500000000000000 : ℝ)*base88 + (787/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((9429/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9429/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37809/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37809/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2276/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2276/3125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6499/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6499/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1641/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1641/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15757/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15757/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307063_s3 p hpa hpb X hX hprev2

#print axioms solution

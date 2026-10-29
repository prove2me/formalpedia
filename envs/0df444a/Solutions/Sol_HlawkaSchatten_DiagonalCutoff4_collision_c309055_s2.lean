-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309055_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:03:49.765709+00:00
-- url     : https://prove2.me/submissions/e900b672-1573-4d8e-b25d-9027ccdd1fb8

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
theorem collision_support_c309055_s2_s2_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-377602193/2500000000 : ℝ)*x 0 + (5905993713/10000000000 : ℝ)*x 1 + (5012159199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (377602193/2500000000 : ℝ)^35 ≤ (215676709181/2500000000000 : ℝ)^27 := by
    have hnat : (377602193 : ℕ)^35*2500000000000^27 ≤ 215676709181^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377602193 2500000000 215676709181 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5905993713/10000000000 : ℝ)^35 ≤ (25263757370647/50000000000000 : ℝ)^27 := by
    have hnat : (5905993713 : ℕ)^35*50000000000000^27 ≤ 25263757370647^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5905993713 10000000000 25263757370647 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5012159199/10000000000 : ℝ)^35 ≤ (40845416879573/100000000000000 : ℝ)^27 := by
    have hnat : (5012159199 : ℕ)^35*100000000000000^27 ≤ 40845416879573^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5012159199 10000000000 40845416879573 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-377602193/2500000000 : ℝ), (5905993713/10000000000 : ℝ), (5012159199/10000000000 : ℝ)] ![(215676709181/2500000000000 : ℝ), (25263757370647/50000000000000 : ℝ), (40845416879573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-377602193/2500000000 : ℝ)|^35 ≤ (215676709181/2500000000000 : ℝ)^27
        have hw : |(-377602193/2500000000 : ℝ)|=(377602193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5905993713/10000000000 : ℝ)|^35 ≤ (25263757370647/50000000000000 : ℝ)^27
        have hw : |(5905993713/10000000000 : ℝ)|=(5905993713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5012159199/10000000000 : ℝ)|^35 ≤ (40845416879573/100000000000000 : ℝ)^27
        have hw : |(5012159199/10000000000 : ℝ)|=(5012159199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s2_s2_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2441459153/5000000000 : ℝ)*x 0 + (-435419267/10000000000 : ℝ)*x 1 + (829790277/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2441459153/5000000000 : ℝ)^35 ≤ (9871345294593/25000000000000 : ℝ)^27 := by
    have hnat : (2441459153 : ℕ)^35*25000000000000^27 ≤ 9871345294593^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2441459153 5000000000 9871345294593 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (435419267/10000000000 : ℝ)^35 ≤ (86018333071/5000000000000 : ℝ)^27 := by
    have hnat : (435419267 : ℕ)^35*5000000000000^27 ≤ 86018333071^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435419267 10000000000 86018333071 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (829790277/1250000000 : ℝ)^35 ≤ (58794252141243/100000000000000 : ℝ)^27 := by
    have hnat : (829790277 : ℕ)^35*100000000000000^27 ≤ 58794252141243^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829790277 1250000000 58794252141243 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2441459153/5000000000 : ℝ), (-435419267/10000000000 : ℝ), (829790277/1250000000 : ℝ)] ![(9871345294593/25000000000000 : ℝ), (86018333071/5000000000000 : ℝ), (58794252141243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2441459153/5000000000 : ℝ)|^35 ≤ (9871345294593/25000000000000 : ℝ)^27
        have hw : |(2441459153/5000000000 : ℝ)|=(2441459153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-435419267/10000000000 : ℝ)|^35 ≤ (86018333071/5000000000000 : ℝ)^27
        have hw : |(-435419267/10000000000 : ℝ)|=(435419267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(829790277/1250000000 : ℝ)|^35 ≤ (58794252141243/100000000000000 : ℝ)^27
        have hw : |(829790277/1250000000 : ℝ)|=(829790277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s2_s2_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (486291473/1000000000 : ℝ)*x 0 + (6070585173/10000000000 : ℝ)*x 1 + (-737364647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (486291473/1000000000 : ℝ)^35 ≤ (39275822869193/100000000000000 : ℝ)^27 := by
    have hnat : (486291473 : ℕ)^35*100000000000000^27 ≤ 39275822869193^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486291473 1000000000 39275822869193 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6070585173/10000000000 : ℝ)^35 ≤ (10472070790099/20000000000000 : ℝ)^27 := by
    have hnat : (6070585173 : ℕ)^35*20000000000000^27 ≤ 10472070790099^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6070585173 10000000000 10472070790099 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (737364647/5000000000 : ℝ)^35 ≤ (4181911588123/50000000000000 : ℝ)^27 := by
    have hnat : (737364647 : ℕ)^35*50000000000000^27 ≤ 4181911588123^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737364647 5000000000 4181911588123 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(486291473/1000000000 : ℝ), (6070585173/10000000000 : ℝ), (-737364647/5000000000 : ℝ)] ![(39275822869193/100000000000000 : ℝ), (10472070790099/20000000000000 : ℝ), (4181911588123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(486291473/1000000000 : ℝ)|^35 ≤ (39275822869193/100000000000000 : ℝ)^27
        have hw : |(486291473/1000000000 : ℝ)|=(486291473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6070585173/10000000000 : ℝ)|^35 ≤ (10472070790099/20000000000000 : ℝ)^27
        have hw : |(6070585173/10000000000 : ℝ)|=(6070585173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-737364647/5000000000 : ℝ)|^35 ≤ (4181911588123/50000000000000 : ℝ)^27
        have hw : |(-737364647/5000000000 : ℝ)|=(737364647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s2_s2_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-221610247/1250000000 : ℝ)*x 0 + (763878977/2000000000 : ℝ)*x 1 + (1360123607/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221610247/1250000000 : ℝ)^35 ≤ (10618579906581/100000000000000 : ℝ)^27 := by
    have hnat : (221610247 : ℕ)^35*100000000000000^27 ≤ 10618579906581^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221610247 1250000000 10618579906581 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (763878977/2000000000 : ℝ)^35 ≤ (14358567145127/50000000000000 : ℝ)^27 := by
    have hnat : (763878977 : ℕ)^35*50000000000000^27 ≤ 14358567145127^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      763878977 2000000000 14358567145127 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360123607/2000000000 : ℝ)^35 ≤ (60664285780791/100000000000000 : ℝ)^27 := by
    have hnat : (1360123607 : ℕ)^35*100000000000000^27 ≤ 60664285780791^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360123607 2000000000 60664285780791 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221610247/1250000000 : ℝ), (763878977/2000000000 : ℝ), (1360123607/2000000000 : ℝ)] ![(10618579906581/100000000000000 : ℝ), (14358567145127/50000000000000 : ℝ), (60664285780791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221610247/1250000000 : ℝ)|^35 ≤ (10618579906581/100000000000000 : ℝ)^27
        have hw : |(-221610247/1250000000 : ℝ)|=(221610247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(763878977/2000000000 : ℝ)|^35 ≤ (14358567145127/50000000000000 : ℝ)^27
        have hw : |(763878977/2000000000 : ℝ)|=(763878977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360123607/2000000000 : ℝ)|^35 ≤ (60664285780791/100000000000000 : ℝ)^27
        have hw : |(1360123607/2000000000 : ℝ)|=(1360123607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s2_s2_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (410119583/1250000000 : ℝ)*x 0 + (17327/2000000000 : ℝ)*x 1 + (1625251879/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410119583/1250000000 : ℝ)^35 ≤ (4716536816021/20000000000000 : ℝ)^27 := by
    have hnat : (410119583 : ℕ)^35*20000000000000^27 ≤ 4716536816021^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410119583 1250000000 4716536816021 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17327/2000000000 : ℝ)^35 ≤ (3425001/12500000000000 : ℝ)^27 := by
    have hnat : (17327 : ℕ)^35*12500000000000^27 ≤ 3425001^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17327 2000000000 3425001 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1625251879/2000000000 : ℝ)^35 ≤ (1910432212819/2500000000000 : ℝ)^27 := by
    have hnat : (1625251879 : ℕ)^35*2500000000000^27 ≤ 1910432212819^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625251879 2000000000 1910432212819 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(410119583/1250000000 : ℝ), (17327/2000000000 : ℝ), (1625251879/2000000000 : ℝ)] ![(4716536816021/20000000000000 : ℝ), (3425001/12500000000000 : ℝ), (1910432212819/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(410119583/1250000000 : ℝ)|^35 ≤ (4716536816021/20000000000000 : ℝ)^27
        have hw : |(410119583/1250000000 : ℝ)|=(410119583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17327/2000000000 : ℝ)|^35 ≤ (3425001/12500000000000 : ℝ)^27
        have hw : |(17327/2000000000 : ℝ)|=(17327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1625251879/2000000000 : ℝ)|^35 ≤ (1910432212819/2500000000000 : ℝ)^27
        have hw : |(1625251879/2000000000 : ℝ)|=(1625251879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s2_s2_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (101784293/312500000 : ℝ)*x 0 + (388038051/500000000 : ℝ)*x 1 + (-58578337/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101784293/312500000 : ℝ)^35 ≤ (23360616294613/100000000000000 : ℝ)^27 := by
    have hnat : (101784293 : ℕ)^35*100000000000000^27 ≤ 23360616294613^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101784293 312500000 23360616294613 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388038051/500000000 : ℝ)^35 ≤ (71991855174189/100000000000000 : ℝ)^27 := by
    have hnat : (388038051 : ℕ)^35*100000000000000^27 ≤ 71991855174189^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388038051 500000000 71991855174189 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58578337/625000000 : ℝ)^35 ≤ (929505705107/20000000000000 : ℝ)^27 := by
    have hnat : (58578337 : ℕ)^35*20000000000000^27 ≤ 929505705107^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58578337 625000000 929505705107 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(101784293/312500000 : ℝ), (388038051/500000000 : ℝ), (-58578337/625000000 : ℝ)] ![(23360616294613/100000000000000 : ℝ), (71991855174189/100000000000000 : ℝ), (929505705107/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(101784293/312500000 : ℝ)|^35 ≤ (23360616294613/100000000000000 : ℝ)^27
        have hw : |(101784293/312500000 : ℝ)|=(101784293/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(388038051/500000000 : ℝ)|^35 ≤ (71991855174189/100000000000000 : ℝ)^27
        have hw : |(388038051/500000000 : ℝ)|=(388038051/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-58578337/625000000 : ℝ)|^35 ≤ (929505705107/20000000000000 : ℝ)^27
        have hw : |(-58578337/625000000 : ℝ)|=(58578337/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s2_s2_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4317335797/10000000000 : ℝ)*x 0 + (671110709/1000000000 : ℝ)*x 1 + (621927753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317335797/10000000000 : ℝ)^35 ≤ (33661357787801/100000000000000 : ℝ)^27 := by
    have hnat : (4317335797 : ℕ)^35*100000000000000^27 ≤ 33661357787801^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317335797 10000000000 33661357787801 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (671110709/1000000000 : ℝ)^35 ≤ (59631251309739/100000000000000 : ℝ)^27 := by
    have hnat : (671110709 : ℕ)^35*100000000000000^27 ≤ 59631251309739^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671110709 1000000000 59631251309739 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (621927753/5000000000 : ℝ)^35 ≤ (6707390891383/100000000000000 : ℝ)^27 := by
    have hnat : (621927753 : ℕ)^35*100000000000000^27 ≤ 6707390891383^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621927753 5000000000 6707390891383 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317335797/10000000000 : ℝ), (671110709/1000000000 : ℝ), (621927753/5000000000 : ℝ)] ![(33661357787801/100000000000000 : ℝ), (59631251309739/100000000000000 : ℝ), (6707390891383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317335797/10000000000 : ℝ)|^35 ≤ (33661357787801/100000000000000 : ℝ)^27
        have hw : |(4317335797/10000000000 : ℝ)|=(4317335797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(671110709/1000000000 : ℝ)|^35 ≤ (59631251309739/100000000000000 : ℝ)^27
        have hw : |(671110709/1000000000 : ℝ)|=(671110709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(621927753/5000000000 : ℝ)|^35 ≤ (6707390891383/100000000000000 : ℝ)^27
        have hw : |(621927753/5000000000 : ℝ)|=(621927753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s2_s2_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-279787759/5000000000 : ℝ)*x 0 + (856699607/2000000000 : ℝ)*x 1 + (1778204967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279787759/5000000000 : ℝ)^35 ≤ (476303609909/20000000000000 : ℝ)^27 := by
    have hnat : (279787759 : ℕ)^35*20000000000000^27 ≤ 476303609909^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279787759 5000000000 476303609909 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (856699607/2000000000 : ℝ)^35 ≤ (33319759083441/100000000000000 : ℝ)^27 := by
    have hnat : (856699607 : ℕ)^35*100000000000000^27 ≤ 33319759083441^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856699607 2000000000 33319759083441 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1778204967/2500000000 : ℝ)^35 ≤ (32149361425937/50000000000000 : ℝ)^27 := by
    have hnat : (1778204967 : ℕ)^35*50000000000000^27 ≤ 32149361425937^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778204967 2500000000 32149361425937 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-279787759/5000000000 : ℝ), (856699607/2000000000 : ℝ), (1778204967/2500000000 : ℝ)] ![(476303609909/20000000000000 : ℝ), (33319759083441/100000000000000 : ℝ), (32149361425937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-279787759/5000000000 : ℝ)|^35 ≤ (476303609909/20000000000000 : ℝ)^27
        have hw : |(-279787759/5000000000 : ℝ)|=(279787759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(856699607/2000000000 : ℝ)|^35 ≤ (33319759083441/100000000000000 : ℝ)^27
        have hw : |(856699607/2000000000 : ℝ)|=(856699607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1778204967/2500000000 : ℝ)|^35 ≤ (32149361425937/50000000000000 : ℝ)^27
        have hw : |(1778204967/2500000000 : ℝ)|=(1778204967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s2_s2_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2740960807/10000000000 : ℝ)*x 0 + (-68677913/2000000000 : ℝ)*x 1 + (4211596017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2740960807/10000000000 : ℝ)^35 ≤ (9339540699861/50000000000000 : ℝ)^27 := by
    have hnat : (2740960807 : ℕ)^35*50000000000000^27 ≤ 9339540699861^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740960807 10000000000 9339540699861 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68677913/2000000000 : ℝ)^35 ≤ (1264579777223/100000000000000 : ℝ)^27 := by
    have hnat : (68677913 : ℕ)^35*100000000000000^27 ≤ 1264579777223^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68677913 2000000000 1264579777223 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4211596017/5000000000 : ℝ)^35 ≤ (40028169403241/50000000000000 : ℝ)^27 := by
    have hnat : (4211596017 : ℕ)^35*50000000000000^27 ≤ 40028169403241^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211596017 5000000000 40028169403241 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2740960807/10000000000 : ℝ), (-68677913/2000000000 : ℝ), (4211596017/5000000000 : ℝ)] ![(9339540699861/50000000000000 : ℝ), (1264579777223/100000000000000 : ℝ), (40028169403241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2740960807/10000000000 : ℝ)|^35 ≤ (9339540699861/50000000000000 : ℝ)^27
        have hw : |(2740960807/10000000000 : ℝ)|=(2740960807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-68677913/2000000000 : ℝ)|^35 ≤ (1264579777223/100000000000000 : ℝ)^27
        have hw : |(-68677913/2000000000 : ℝ)|=(68677913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4211596017/5000000000 : ℝ)|^35 ≤ (40028169403241/50000000000000 : ℝ)^27
        have hw : |(4211596017/5000000000 : ℝ)|=(4211596017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s2_s2_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6955262799/10000000000 : ℝ)*x 0 + (4477568591/10000000000 : ℝ)*x 1 + (-267960051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6955262799/10000000000 : ℝ)^35 ≤ (12491702336177/20000000000000 : ℝ)^27 := by
    have hnat : (6955262799 : ℕ)^35*20000000000000^27 ≤ 12491702336177^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6955262799 10000000000 12491702336177 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477568591/10000000000 : ℝ)^35 ≤ (882241263643/2500000000000 : ℝ)^27 := by
    have hnat : (4477568591 : ℕ)^35*2500000000000^27 ≤ 882241263643^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477568591 10000000000 882241263643 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267960051/5000000000 : ℝ)^35 ≤ (450367553243/20000000000000 : ℝ)^27 := by
    have hnat : (267960051 : ℕ)^35*20000000000000^27 ≤ 450367553243^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267960051 5000000000 450367553243 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6955262799/10000000000 : ℝ), (4477568591/10000000000 : ℝ), (-267960051/5000000000 : ℝ)] ![(12491702336177/20000000000000 : ℝ), (882241263643/2500000000000 : ℝ), (450367553243/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6955262799/10000000000 : ℝ)|^35 ≤ (12491702336177/20000000000000 : ℝ)^27
        have hw : |(6955262799/10000000000 : ℝ)|=(6955262799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477568591/10000000000 : ℝ)|^35 ≤ (882241263643/2500000000000 : ℝ)^27
        have hw : |(4477568591/10000000000 : ℝ)|=(4477568591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-267960051/5000000000 : ℝ)|^35 ≤ (450367553243/20000000000000 : ℝ)^27
        have hw : |(-267960051/5000000000 : ℝ)|=(267960051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s2_s2_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (528445851/625000000 : ℝ)*x 0 + (1217334909/5000000000 : ℝ)*x 1 + (758169239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528445851/625000000 : ℝ)^35 ≤ (80450091396369/100000000000000 : ℝ)^27 := by
    have hnat : (528445851 : ℕ)^35*100000000000000^27 ≤ 80450091396369^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528445851 625000000 80450091396369 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1217334909/5000000000 : ℝ)^35 ≤ (16019336997543/100000000000000 : ℝ)^27 := by
    have hnat : (1217334909 : ℕ)^35*100000000000000^27 ≤ 16019336997543^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217334909 5000000000 16019336997543 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (758169239/10000000000 : ℝ)^35 ≤ (353057158961/10000000000000 : ℝ)^27 := by
    have hnat : (758169239 : ℕ)^35*10000000000000^27 ≤ 353057158961^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758169239 10000000000 353057158961 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528445851/625000000 : ℝ), (1217334909/5000000000 : ℝ), (758169239/10000000000 : ℝ)] ![(80450091396369/100000000000000 : ℝ), (16019336997543/100000000000000 : ℝ), (353057158961/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528445851/625000000 : ℝ)|^35 ≤ (80450091396369/100000000000000 : ℝ)^27
        have hw : |(528445851/625000000 : ℝ)|=(528445851/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1217334909/5000000000 : ℝ)|^35 ≤ (16019336997543/100000000000000 : ℝ)^27
        have hw : |(1217334909/5000000000 : ℝ)|=(1217334909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(758169239/10000000000 : ℝ)|^35 ≤ (353057158961/10000000000000 : ℝ)^27
        have hw : |(758169239/10000000000 : ℝ)|=(758169239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s2_s2_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-904082149/10000000000 : ℝ)*x 0 + (3775315463/5000000000 : ℝ)*x 1 + (88671209/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (904082149/10000000000 : ℝ)^35 ≤ (4435434387429/100000000000000 : ℝ)^27 := by
    have hnat : (904082149 : ℕ)^35*100000000000000^27 ≤ 4435434387429^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904082149 10000000000 4435434387429 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3775315463/5000000000 : ℝ)^35 ≤ (69475251755633/100000000000000 : ℝ)^27 := by
    have hnat : (3775315463 : ℕ)^35*100000000000000^27 ≤ 69475251755633^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3775315463 5000000000 69475251755633 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88671209/250000000 : ℝ)^35 ≤ (5217862769149/20000000000000 : ℝ)^27 := by
    have hnat : (88671209 : ℕ)^35*20000000000000^27 ≤ 5217862769149^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88671209 250000000 5217862769149 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-904082149/10000000000 : ℝ), (3775315463/5000000000 : ℝ), (88671209/250000000 : ℝ)] ![(4435434387429/100000000000000 : ℝ), (69475251755633/100000000000000 : ℝ), (5217862769149/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-904082149/10000000000 : ℝ)|^35 ≤ (4435434387429/100000000000000 : ℝ)^27
        have hw : |(-904082149/10000000000 : ℝ)|=(904082149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3775315463/5000000000 : ℝ)|^35 ≤ (69475251755633/100000000000000 : ℝ)^27
        have hw : |(3775315463/5000000000 : ℝ)|=(3775315463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(88671209/250000000 : ℝ)|^35 ≤ (5217862769149/20000000000000 : ℝ)^27
        have hw : |(88671209/250000000 : ℝ)|=(88671209/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s2_s2_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (43676147/62500000 : ℝ)*x 0 + (-1987461/1250000000 : ℝ)*x 1 + (186283143/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43676147/62500000 : ℝ)^35 ≤ (62842003228227/100000000000000 : ℝ)^27 := by
    have hnat : (43676147 : ℕ)^35*100000000000000^27 ≤ 62842003228227^27*62500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43676147 62500000 62842003228227 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1987461/1250000000 : ℝ)^35 ≤ (11779867747/50000000000000 : ℝ)^27 := by
    have hnat : (1987461 : ℕ)^35*50000000000000^27 ≤ 11779867747^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987461 1250000000 11779867747 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (186283143/400000000 : ℝ)^35 ≤ (37134437020327/100000000000000 : ℝ)^27 := by
    have hnat : (186283143 : ℕ)^35*100000000000000^27 ≤ 37134437020327^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186283143 400000000 37134437020327 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43676147/62500000 : ℝ), (-1987461/1250000000 : ℝ), (186283143/400000000 : ℝ)] ![(62842003228227/100000000000000 : ℝ), (11779867747/50000000000000 : ℝ), (37134437020327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43676147/62500000 : ℝ)|^35 ≤ (62842003228227/100000000000000 : ℝ)^27
        have hw : |(43676147/62500000 : ℝ)|=(43676147/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1987461/1250000000 : ℝ)|^35 ≤ (11779867747/50000000000000 : ℝ)^27
        have hw : |(-1987461/1250000000 : ℝ)|=(1987461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(186283143/400000000 : ℝ)|^35 ≤ (37134437020327/100000000000000 : ℝ)^27
        have hw : |(186283143/400000000 : ℝ)|=(186283143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s2_s2_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2401376967/10000000000 : ℝ)*x 0 + (250483141/312500000 : ℝ)*x 1 + (-1586507/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2401376967/10000000000 : ℝ)^35 ≤ (7867976219837/50000000000000 : ℝ)^27 := by
    have hnat : (2401376967 : ℕ)^35*50000000000000^27 ≤ 7867976219837^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401376967 10000000000 7867976219837 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250483141/312500000 : ℝ)^35 ≤ (586479550163/781250000000 : ℝ)^27 := by
    have hnat : (250483141 : ℕ)^35*781250000000^27 ≤ 586479550163^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250483141 312500000 586479550163 781250000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1586507/10000000 : ℝ)^35 ≤ (4597332560133/50000000000000 : ℝ)^27 := by
    have hnat : (1586507 : ℕ)^35*50000000000000^27 ≤ 4597332560133^27*10000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586507 10000000 4597332560133 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2401376967/10000000000 : ℝ), (250483141/312500000 : ℝ), (-1586507/10000000 : ℝ)] ![(7867976219837/50000000000000 : ℝ), (586479550163/781250000000 : ℝ), (4597332560133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2401376967/10000000000 : ℝ)|^35 ≤ (7867976219837/50000000000000 : ℝ)^27
        have hw : |(2401376967/10000000000 : ℝ)|=(2401376967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(250483141/312500000 : ℝ)|^35 ≤ (586479550163/781250000000 : ℝ)^27
        have hw : |(250483141/312500000 : ℝ)|=(250483141/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1586507/10000000 : ℝ)|^35 ≤ (4597332560133/50000000000000 : ℝ)^27
        have hw : |(-1586507/10000000 : ℝ)|=(1586507/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309055_s2_s2_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8215188527/10000000000 : ℝ)*x 0 + (2124069633/10000000000 : ℝ)*x 1 + (196320873/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8215188527/10000000000 : ℝ)^35 ≤ (1937577286063/2500000000000 : ℝ)^27 := by
    have hnat : (8215188527 : ℕ)^35*2500000000000^27 ≤ 1937577286063^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8215188527 10000000000 1937577286063 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124069633/10000000000 : ℝ)^35 ≤ (6710908956193/50000000000000 : ℝ)^27 := by
    have hnat : (2124069633 : ℕ)^35*50000000000000^27 ≤ 6710908956193^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124069633 10000000000 6710908956193 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196320873/1250000000 : ℝ)^35 ≤ (9075090639311/100000000000000 : ℝ)^27 := by
    have hnat : (196320873 : ℕ)^35*100000000000000^27 ≤ 9075090639311^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196320873 1250000000 9075090639311 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8215188527/10000000000 : ℝ), (2124069633/10000000000 : ℝ), (196320873/1250000000 : ℝ)] ![(1937577286063/2500000000000 : ℝ), (6710908956193/50000000000000 : ℝ), (9075090639311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8215188527/10000000000 : ℝ)|^35 ≤ (1937577286063/2500000000000 : ℝ)^27
        have hw : |(8215188527/10000000000 : ℝ)|=(8215188527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2124069633/10000000000 : ℝ)|^35 ≤ (6710908956193/50000000000000 : ℝ)^27
        have hw : |(2124069633/10000000000 : ℝ)|=(2124069633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(196320873/1250000000 : ℝ)|^35 ≤ (9075090639311/100000000000000 : ℝ)^27
        have hw : |(196320873/1250000000 : ℝ)|=(196320873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309055_s2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((40601/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40601/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79067/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79067/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39949/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(39949/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6869/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6869/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(67259/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(67259/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34371/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(34371/50000 : ℝ)*X 1 2) := by
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
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91323/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s2_pow0 : (40601/50000 : ℝ) ^ (69/16 : ℝ) ≤ (40738638061340566191/100000000000000000000 : ℝ) := by
    have hpowers : (40601/50000 : ℝ)^69 ≤ (40738638061340566191/100000000000000000000 : ℝ)^16 := by
      have hnat : (40601 : ℕ)^69*100000000000000000000^16 ≤ 40738638061340566191^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40601 50000 40738638061340566191 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40601/50000 : ℝ)) (X := (40738638061340566191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (140738638061340566191/100000000000000000000 : ℝ) ≤ (5412335287941291/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (140738638061340566191/100000000000000000000 : ℝ)^16 ≤ (5412335287941291/5000000000000000 : ℝ)^69 := by
      have hnat : (140738638061340566191 : ℕ)^16*5000000000000000^69 ≤ 5412335287941291^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        140738638061340566191 100000000000000000000 5412335287941291 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5412335287941291/5000000000000000 : ℝ)) (X := (140738638061340566191/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (90738638061340566191/50000000000000000000 : ℝ) ≤ (5740989577797631/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (90738638061340566191/50000000000000000000 : ℝ)^16 ≤ (5740989577797631/5000000000000000 : ℝ)^69 := by
      have hnat : (90738638061340566191 : ℕ)^16*5000000000000000^69 ≤ 5740989577797631^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        90738638061340566191 50000000000000000000 5740989577797631 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5740989577797631/5000000000000000 : ℝ)) (X := (90738638061340566191/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(37485026176481/369100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(16432714492817/203005000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (40601/50000 : ℝ)) (alpha := (37485026176481/369100000000000 : ℝ)) (beta := (16432714492817/203005000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (40601/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(37485026176481/369100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(16432714492817/203005000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (79067/100000 : ℝ) ^ (69/16 : ℝ) ≤ (7263309630230436599/20000000000000000000 : ℝ) := by
    have hpowers : (79067/100000 : ℝ)^69 ≤ (7263309630230436599/20000000000000000000 : ℝ)^16 := by
      have hnat : (79067 : ℕ)^69*20000000000000000000^16 ≤ 7263309630230436599^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79067 100000 7263309630230436599 20000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79067/100000 : ℝ)) (X := (7263309630230436599/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (27263309630230436599/20000000000000000000 : ℝ) ≤ (10744833021170913/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (27263309630230436599/20000000000000000000 : ℝ)^16 ≤ (10744833021170913/10000000000000000 : ℝ)^69 := by
      have hnat : (27263309630230436599 : ℕ)^16*10000000000000000^69 ≤ 10744833021170913^69*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27263309630230436599 20000000000000000000 10744833021170913 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10744833021170913/10000000000000000 : ℝ)) (X := (27263309630230436599/20000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (17263309630230436599/10000000000000000000 : ℝ) ≤ (2837430926116519/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (17263309630230436599/10000000000000000000 : ℝ)^16 ≤ (2837430926116519/2500000000000000 : ℝ)^69 := by
      have hnat : (17263309630230436599 : ℕ)^16*2500000000000000^69 ≤ 2837430926116519^69*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17263309630230436599 10000000000000000000 2837430926116519 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2837430926116519/2500000000000000 : ℝ)) (X := (17263309630230436599/10000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(744833021170913/7906700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(604890683295163/7906700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (79067/100000 : ℝ)) (alpha := (744833021170913/7906700000000000 : ℝ)) (beta := (604890683295163/7906700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (79067/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(744833021170913/7906700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(604890683295163/7906700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (39949/50000 : ℝ) ^ (69/16 : ℝ) ≤ (9497867636438300261/25000000000000000000 : ℝ) := by
    have hpowers : (39949/50000 : ℝ)^69 ≤ (9497867636438300261/25000000000000000000 : ℝ)^16 := by
      have hnat : (39949 : ℕ)^69*25000000000000000000^16 ≤ 9497867636438300261^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39949 50000 9497867636438300261 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39949/50000 : ℝ)) (X := (9497867636438300261/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (34497867636438300261/25000000000000000000 : ℝ) ≤ (538765167721929/500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (34497867636438300261/25000000000000000000 : ℝ)^16 ≤ (538765167721929/500000000000000 : ℝ)^69 := by
      have hnat : (34497867636438300261 : ℕ)^16*500000000000000^69 ≤ 538765167721929^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34497867636438300261 25000000000000000000 538765167721929 500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (538765167721929/500000000000000 : ℝ)) (X := (34497867636438300261/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (21997867636438300261/12500000000000000000 : ℝ) ≤ (11400416347784921/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (21997867636438300261/12500000000000000000 : ℝ)^16 ≤ (11400416347784921/10000000000000000 : ℝ)^69 := by
      have hnat : (21997867636438300261 : ℕ)^16*10000000000000000^69 ≤ 11400416347784921^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21997867636438300261 12500000000000000000 11400416347784921 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11400416347784921/10000000000000000 : ℝ)) (X := (21997867636438300261/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(38765167721929/399490000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(625112993346341/7989800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (39949/50000 : ℝ)) (alpha := (38765167721929/399490000000000 : ℝ)) (beta := (625112993346341/7989800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (39949/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(38765167721929/399490000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(625112993346341/7989800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-377602193/2500000000 : ℝ)*X 0 0+(5905993713/10000000000 : ℝ)*X 0 1+(5012159199/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((2441459153/5000000000 : ℝ)*X 1 0+(-435419267/10000000000 : ℝ)*X 1 1+(829790277/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((486291473/1000000000 : ℝ)*X 2 0+(6070585173/10000000000 : ℝ)*X 2 1+(-737364647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-221610247/1250000000 : ℝ)*X 0 0+(763878977/2000000000 : ℝ)*X 0 1+(1360123607/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((410119583/1250000000 : ℝ)*X 1 0+(17327/2000000000 : ℝ)*X 1 1+(1625251879/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((101784293/312500000 : ℝ)*X 2 0+(388038051/500000000 : ℝ)*X 2 1+(-58578337/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((4317335797/10000000000 : ℝ)*X 0 0+(671110709/1000000000 : ℝ)*X 0 1+(621927753/5000000000 : ℝ)*X 0 2+(4317335797/10000000000 : ℝ)*X 1 0+(671110709/1000000000 : ℝ)*X 1 1+(621927753/5000000000 : ℝ)*X 1 2+(4317335797/10000000000 : ℝ)*X 2 0+(671110709/1000000000 : ℝ)*X 2 1+(621927753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-279787759/5000000000 : ℝ)*X 0 0+(856699607/2000000000 : ℝ)*X 0 1+(1778204967/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2740960807/10000000000 : ℝ)*X 1 0+(-68677913/2000000000 : ℝ)*X 1 1+(4211596017/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6955262799/10000000000 : ℝ)*X 2 0+(4477568591/10000000000 : ℝ)*X 2 1+(-267960051/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((528445851/625000000 : ℝ)*X 0 0+(1217334909/5000000000 : ℝ)*X 0 1+(758169239/10000000000 : ℝ)*X 0 2+(528445851/625000000 : ℝ)*X 1 0+(1217334909/5000000000 : ℝ)*X 1 1+(758169239/10000000000 : ℝ)*X 1 2+(528445851/625000000 : ℝ)*X 2 0+(1217334909/5000000000 : ℝ)*X 2 1+(758169239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-904082149/10000000000 : ℝ)*X 0 0+(3775315463/5000000000 : ℝ)*X 0 1+(88671209/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((43676147/62500000 : ℝ)*X 1 0+(-1987461/1250000000 : ℝ)*X 1 1+(186283143/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2401376967/10000000000 : ℝ)*X 2 0+(250483141/312500000 : ℝ)*X 2 1+(-1586507/10000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((8215188527/10000000000 : ℝ)*X 0 0+(2124069633/10000000000 : ℝ)*X 0 1+(196320873/1250000000 : ℝ)*X 0 2+(8215188527/10000000000 : ℝ)*X 1 0+(2124069633/10000000000 : ℝ)*X 1 1+(196320873/1250000000 : ℝ)*X 1 2+(8215188527/10000000000 : ℝ)*X 2 0+(2124069633/10000000000 : ℝ)*X 2 1+(196320873/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309055_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((6869/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6869/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (360727678621507792310105793/24297289100000000000000000000000 : ℝ) := by norm_num
    linear_combination (680588980229/1000000000000 : ℝ)*(base7) + (2449809/1000000000000 : ℝ)*(base49) + (2383609/1000000000000 : ℝ)*(base53) + (475157/500000000000 : ℝ)*(base60) + (2248162502259/1000000000000 : ℝ)*(major_s2_0) + (2248162502259/1000000000000 : ℝ)*(major_s2_1) + (2248160118649/1000000000000 : ℝ)*(major_s2_2) + (21479051/1000000000000 : ℝ)*(sp_s2_0) + (534032139619/200000000000 : ℝ)*(sp_s2_7) + (166888493597/62500000000 : ℝ)*(sp_s2_8) + (1335100032851/500000000000 : ℝ)*(sp_s2_9) + (2092334571831/1000000000000 : ℝ)*(sp_s2_13) + (16860203/500000000000 : ℝ)*(sp_s2_14) + (18215459/1000000000000 : ℝ)*(sp_s2_23) + (705872795801/500000000000 : ℝ)*(f.failure) + (2670218281161/1000000000000 : ℝ)*(f.sum) + (152391465417149743443/315864758300000000000000000000000 : ℝ)*base63 + (769194841259931/7989800000000000000000000000 : ℝ)*base64 + (925513132890223/7906700000000000000000000000 : ℝ)*base67 + (147926228308253/199745000000000000000000000 : ℝ)*base69 + (7617014079671681339/29490351800000000000000000000000 : ℝ)*base70 + (3906813709023/10150250000000000000000000 : ℝ)*base72 + (4110679699487427/7906700000000000000000000000 : ℝ)*base75 + (243717823719999/369100000000000000000000000 : ℝ)*base77 + (149319103444629108263/321019926700000000000000000000000 : ℝ)*base79 + (28153/50000000000000000 : ℝ)*base86 + (28153/50000000000000000 : ℝ)*base88 + (21847/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(67259/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(67259/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34381073000249042134406583/3037161137500000000000000000000 : ℝ) := by norm_num
    linear_combination (13746663587/25000000000 : ℝ)*(base7) + (147111/25000000000 : ℝ)*(base27) + (2069/125000000000 : ℝ)*(base59) + (245479613989/125000000000 : ℝ)*(major_s2_0) + (245479613989/125000000000 : ℝ)*(major_s2_1) + (245479613989/125000000000 : ℝ)*(major_s2_2) + (21361343/1000000000000 : ℝ)*(sp_s2_0) + (21548021/1000000000000 : ℝ)*(sp_s2_2) + (1295659/7812500000 : ℝ)*(sp_s2_8) + (2359677114061/1000000000000 : ℝ)*(sp_s2_14) + (589883157763/250000000000 : ℝ)*(sp_s2_15) + (2359676927383/1000000000000 : ℝ)*(sp_s2_16) + (891509361473/500000000000 : ℝ)*(sp_s2_20) + (43762133/1000000000000 : ℝ)*(sp_s2_27) + (1233201826039/1000000000000 : ℝ)*(f.failure) + (589924618851/250000000000 : ℝ)*(f.sum) + (21192990164904538343/157932379150000000000000000000000 : ℝ)*base62 + (163897875644803/1997450000000000000000000000 : ℝ)*base65 + (305922715748113/3953350000000000000000000000 : ℝ)*base66 + (80361411824283/399490000000000000000000000 : ℝ)*base68 + (774134663818352667/7372587950000000000000000000000 : ℝ)*base71 + (9629837776983/203005000000000000000000000 : ℝ)*base72 + (196496907802731/1976675000000000000000000000 : ℝ)*base74 + (35618751289529/184550000000000000000000000 : ℝ)*base76 + (2171652110793281421/80254981675000000000000000000000 : ℝ)*base79 + (32633/100000000000000000 : ℝ)*base87 + (32633/100000000000000000 : ℝ)*base89 + (32633/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34371/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(34371/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6687255964160709943155379883709/582928411442650000000000000000000000 : ℝ) := by norm_num
    linear_combination (175939848821/250000000000 : ℝ)*(base7) + (2867574677/50000000000 : ℝ)*(base40) + (29899/62500000000 : ℝ)*(base43) + (153113/500000000000 : ℝ)*(base59) + (954942981123/500000000000 : ℝ)*(major_s2_0) + (954942741931/500000000000 : ℝ)*(major_s2_1) + (954942981123/500000000000 : ℝ)*(major_s2_2) + (1073771/200000000000 : ℝ)*(sp_s2_1) + (75092907/1000000000000 : ℝ)*(sp_s2_9) + (9955729/500000000000 : ℝ)*(sp_s2_20) + (1095990893329/500000000000 : ℝ)*(sp_s2_21) + (2191976896187/1000000000000 : ℝ)*(sp_s2_22) + (350705071/160000000 : ℝ)*(sp_s2_23) + (190306252429/100000000000 : ℝ)*(sp_s2_27) + (1199323040463/1000000000000 : ℝ)*(f.failure) + (1095991132521/500000000000 : ℝ)*(f.sum) + (56644691877512144403/157932379150000000000000000000000 : ℝ)*base62 + (4140024443462837/3994900000000000000000000000 : ℝ)*base64 + (2189096211874923/3953350000000000000000000000 : ℝ)*base66 + (144411625547619/199745000000000000000000000 : ℝ)*base68 + (12685738787753004083/14745175900000000000000000000000 : ℝ)*base70 + (170301444680263/406010000000000000000000000 : ℝ)*base72 + (2194888049162397/3953350000000000000000000000 : ℝ)*base74 + (453807939907/184550000000000000000000000 : ℝ)*base76 + (8453199139668290257/160509963350000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (11361/100000000000000000 : ℝ)*base87 + (11361/100000000000000000 : ℝ)*base89 + (11361/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((40601/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40601/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79067/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79067/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39949/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(39949/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6869/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6869/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(67259/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(67259/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34371/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(34371/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309055_s2 p hpa hpb X hX hprev1

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:34:56.60398+00:00
-- url     : https://prove2.me/submissions/69b5be94-fbb8-4b6d-872e-188226dd2c14

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
theorem collision_support_c313063_s2_s2_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-570796423/5000000000 : ℝ)*x 0 + (5482145693/10000000000 : ℝ)*x 1 + (2779709293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (570796423/5000000000 : ℝ)^37 ≤ (3136782043267/50000000000000 : ℝ)^29 := by
    have hnat : (570796423 : ℕ)^37*50000000000000^29 ≤ 3136782043267^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570796423 5000000000 3136782043267 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5482145693/10000000000 : ℝ)^37 ≤ (2902798937669/6250000000000 : ℝ)^29 := by
    have hnat : (5482145693 : ℕ)^37*6250000000000^29 ≤ 2902798937669^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482145693 10000000000 2902798937669 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2779709293/5000000000 : ℝ)^37 ≤ (47281652896109/100000000000000 : ℝ)^29 := by
    have hnat : (2779709293 : ℕ)^37*100000000000000^29 ≤ 47281652896109^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2779709293 5000000000 47281652896109 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-570796423/5000000000 : ℝ), (5482145693/10000000000 : ℝ), (2779709293/5000000000 : ℝ)] ![(3136782043267/50000000000000 : ℝ), (2902798937669/6250000000000 : ℝ), (47281652896109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-570796423/5000000000 : ℝ)|^37 ≤ (3136782043267/50000000000000 : ℝ)^29
        have hw : |(-570796423/5000000000 : ℝ)|=(570796423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5482145693/10000000000 : ℝ)|^37 ≤ (2902798937669/6250000000000 : ℝ)^29
        have hw : |(5482145693/10000000000 : ℝ)|=(5482145693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2779709293/5000000000 : ℝ)|^37 ≤ (47281652896109/100000000000000 : ℝ)^29
        have hw : |(2779709293/5000000000 : ℝ)|=(2779709293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s2_s2_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (685295553/1250000000 : ℝ)*x 0 + (-1144322099/10000000000 : ℝ)*x 1 + (1111487297/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (685295553/1250000000 : ℝ)^37 ≤ (46447147303997/100000000000000 : ℝ)^29 := by
    have hnat : (685295553 : ℕ)^37*100000000000000^29 ≤ 46447147303997^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685295553 1250000000 46447147303997 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1144322099/10000000000 : ℝ)^37 ≤ (1258541273871/20000000000000 : ℝ)^29 := by
    have hnat : (1144322099 : ℕ)^37*20000000000000^29 ≤ 1258541273871^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144322099 10000000000 1258541273871 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111487297/2000000000 : ℝ)^37 ≤ (47260146312683/100000000000000 : ℝ)^29 := by
    have hnat : (1111487297 : ℕ)^37*100000000000000^29 ≤ 47260146312683^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111487297 2000000000 47260146312683 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(685295553/1250000000 : ℝ), (-1144322099/10000000000 : ℝ), (1111487297/2000000000 : ℝ)] ![(46447147303997/100000000000000 : ℝ), (1258541273871/20000000000000 : ℝ), (47260146312683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(685295553/1250000000 : ℝ)|^37 ≤ (46447147303997/100000000000000 : ℝ)^29
        have hw : |(685295553/1250000000 : ℝ)|=(685295553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1144322099/10000000000 : ℝ)|^37 ≤ (1258541273871/20000000000000 : ℝ)^29
        have hw : |(-1144322099/10000000000 : ℝ)|=(1144322099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1111487297/2000000000 : ℝ)|^37 ≤ (47260146312683/100000000000000 : ℝ)^29
        have hw : |(1111487297/2000000000 : ℝ)|=(1111487297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s2_s2_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2761684563/5000000000 : ℝ)*x 0 + (1386356333/2500000000 : ℝ)*x 1 + (-1099406851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2761684563/5000000000 : ℝ)^37 ≤ (46890833104429/100000000000000 : ℝ)^29 := by
    have hnat : (2761684563 : ℕ)^37*100000000000000^29 ≤ 46890833104429^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761684563 5000000000 46890833104429 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1386356333/2500000000 : ℝ)^37 ≤ (47129865809869/100000000000000 : ℝ)^29 := by
    have hnat : (1386356333 : ℕ)^37*100000000000000^29 ≤ 47129865809869^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386356333 2500000000 47129865809869 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099406851/10000000000 : ℝ)^37 ≤ (5979301077451/100000000000000 : ℝ)^29 := by
    have hnat : (1099406851 : ℕ)^37*100000000000000^29 ≤ 5979301077451^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099406851 10000000000 5979301077451 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2761684563/5000000000 : ℝ), (1386356333/2500000000 : ℝ), (-1099406851/10000000000 : ℝ)] ![(46890833104429/100000000000000 : ℝ), (47129865809869/100000000000000 : ℝ), (5979301077451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2761684563/5000000000 : ℝ)|^37 ≤ (46890833104429/100000000000000 : ℝ)^29
        have hw : |(2761684563/5000000000 : ℝ)|=(2761684563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1386356333/2500000000 : ℝ)|^37 ≤ (47129865809869/100000000000000 : ℝ)^29
        have hw : |(1386356333/2500000000 : ℝ)|=(1386356333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1099406851/10000000000 : ℝ)|^37 ≤ (5979301077451/100000000000000 : ℝ)^29
        have hw : |(-1099406851/10000000000 : ℝ)|=(1099406851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s2_s2_6 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (268928269/625000000 : ℝ)*x 0 + (2121499291/5000000000 : ℝ)*x 1 + (1033726203/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268928269/625000000 : ℝ)^37 ≤ (34097593792357/100000000000000 : ℝ)^29 := by
    have hnat : (268928269 : ℕ)^37*100000000000000^29 ≤ 34097593792357^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268928269 625000000 34097593792357 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121499291/5000000000 : ℝ)^37 ≤ (4186701247263/12500000000000 : ℝ)^29 := by
    have hnat : (2121499291 : ℕ)^37*12500000000000^29 ≤ 4186701247263^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121499291 5000000000 4186701247263 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033726203/2500000000 : ℝ)^37 ≤ (16204398110839/50000000000000 : ℝ)^29 := by
    have hnat : (1033726203 : ℕ)^37*50000000000000^29 ≤ 16204398110839^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033726203 2500000000 16204398110839 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268928269/625000000 : ℝ), (2121499291/5000000000 : ℝ), (1033726203/2500000000 : ℝ)] ![(34097593792357/100000000000000 : ℝ), (4186701247263/12500000000000 : ℝ), (16204398110839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268928269/625000000 : ℝ)|^37 ≤ (34097593792357/100000000000000 : ℝ)^29
        have hw : |(268928269/625000000 : ℝ)|=(268928269/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2121499291/5000000000 : ℝ)|^37 ≤ (4186701247263/12500000000000 : ℝ)^29
        have hw : |(2121499291/5000000000 : ℝ)|=(2121499291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1033726203/2500000000 : ℝ)|^37 ≤ (16204398110839/50000000000000 : ℝ)^29
        have hw : |(1033726203/2500000000 : ℝ)|=(1033726203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s2_s2_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-907813849/10000000000 : ℝ)*x 0 + (56435869/125000000 : ℝ)*x 1 + (6618357241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (907813849/10000000000 : ℝ)^37 ≤ (468325328239/10000000000000 : ℝ)^29 := by
    have hnat : (907813849 : ℕ)^37*10000000000000^29 ≤ 468325328239^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907813849 10000000000 468325328239 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56435869/125000000 : ℝ)^37 ≤ (1812779241667/5000000000000 : ℝ)^29 := by
    have hnat : (56435869 : ℕ)^37*5000000000000^29 ≤ 1812779241667^29*125000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56435869 125000000 1812779241667 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6618357241/10000000000 : ℝ)^37 ≤ (14765290468539/25000000000000 : ℝ)^29 := by
    have hnat : (6618357241 : ℕ)^37*25000000000000^29 ≤ 14765290468539^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6618357241 10000000000 14765290468539 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-907813849/10000000000 : ℝ), (56435869/125000000 : ℝ), (6618357241/10000000000 : ℝ)] ![(468325328239/10000000000000 : ℝ), (1812779241667/5000000000000 : ℝ), (14765290468539/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-907813849/10000000000 : ℝ)|^37 ≤ (468325328239/10000000000000 : ℝ)^29
        have hw : |(-907813849/10000000000 : ℝ)|=(907813849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56435869/125000000 : ℝ)|^37 ≤ (1812779241667/5000000000000 : ℝ)^29
        have hw : |(56435869/125000000 : ℝ)|=(56435869/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6618357241/10000000000 : ℝ)|^37 ≤ (14765290468539/25000000000000 : ℝ)^29
        have hw : |(6618357241/10000000000 : ℝ)|=(6618357241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s2_s2_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4885091733/10000000000 : ℝ)*x 0 + (-9716407/400000000 : ℝ)*x 1 + (1654084069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4885091733/10000000000 : ℝ)^37 ≤ (40090780299153/100000000000000 : ℝ)^29 := by
    have hnat : (4885091733 : ℕ)^37*100000000000000^29 ≤ 40090780299153^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4885091733 10000000000 40090780299153 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9716407/400000000 : ℝ)^37 ≤ (871066715443/100000000000000 : ℝ)^29 := by
    have hnat : (9716407 : ℕ)^37*100000000000000^29 ≤ 871066715443^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9716407 400000000 871066715443 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1654084069/2500000000 : ℝ)^37 ≤ (14759538241563/25000000000000 : ℝ)^29 := by
    have hnat : (1654084069 : ℕ)^37*25000000000000^29 ≤ 14759538241563^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1654084069 2500000000 14759538241563 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4885091733/10000000000 : ℝ), (-9716407/400000000 : ℝ), (1654084069/2500000000 : ℝ)] ![(40090780299153/100000000000000 : ℝ), (871066715443/100000000000000 : ℝ), (14759538241563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4885091733/10000000000 : ℝ)|^37 ≤ (40090780299153/100000000000000 : ℝ)^29
        have hw : |(4885091733/10000000000 : ℝ)|=(4885091733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9716407/400000000 : ℝ)|^37 ≤ (871066715443/100000000000000 : ℝ)^29
        have hw : |(-9716407/400000000 : ℝ)|=(9716407/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1654084069/2500000000 : ℝ)|^37 ≤ (14759538241563/25000000000000 : ℝ)^29
        have hw : |(1654084069/2500000000 : ℝ)|=(1654084069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s2_s2_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4613814407/10000000000 : ℝ)*x 0 + (689026037/1000000000 : ℝ)*x 1 + (-170207503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4613814407/10000000000 : ℝ)^37 ≤ (2329523350473/6250000000000 : ℝ)^29 := by
    have hnat : (4613814407 : ℕ)^37*6250000000000^29 ≤ 2329523350473^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4613814407 10000000000 2329523350473 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (689026037/1000000000 : ℝ)^37 ≤ (6217431090063/10000000000000 : ℝ)^29 := by
    have hnat : (689026037 : ℕ)^37*10000000000000^29 ≤ 6217431090063^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689026037 1000000000 6217431090063 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170207503/10000000000 : ℝ)^37 ≤ (138328871351/25000000000000 : ℝ)^29 := by
    have hnat : (170207503 : ℕ)^37*25000000000000^29 ≤ 138328871351^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170207503 10000000000 138328871351 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4613814407/10000000000 : ℝ), (689026037/1000000000 : ℝ), (-170207503/10000000000 : ℝ)] ![(2329523350473/6250000000000 : ℝ), (6217431090063/10000000000000 : ℝ), (138328871351/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4613814407/10000000000 : ℝ)|^37 ≤ (2329523350473/6250000000000 : ℝ)^29
        have hw : |(4613814407/10000000000 : ℝ)|=(4613814407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(689026037/1000000000 : ℝ)|^37 ≤ (6217431090063/10000000000000 : ℝ)^29
        have hw : |(689026037/1000000000 : ℝ)|=(689026037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-170207503/10000000000 : ℝ)|^37 ≤ (138328871351/25000000000000 : ℝ)^29
        have hw : |(-170207503/10000000000 : ℝ)|=(170207503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s2_s2_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2219603697/5000000000 : ℝ)*x 0 + (6061612833/10000000000 : ℝ)*x 1 + (1863170487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2219603697/5000000000 : ℝ)^37 ≤ (8870546799099/25000000000000 : ℝ)^29 := by
    have hnat : (2219603697 : ℕ)^37*25000000000000^29 ≤ 8870546799099^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219603697 5000000000 8870546799099 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6061612833/10000000000 : ℝ)^37 ≤ (52797398380971/100000000000000 : ℝ)^29 := by
    have hnat : (6061612833 : ℕ)^37*100000000000000^29 ≤ 52797398380971^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6061612833 10000000000 52797398380971 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1863170487/10000000000 : ℝ)^37 ≤ (5860207204053/50000000000000 : ℝ)^29 := by
    have hnat : (1863170487 : ℕ)^37*50000000000000^29 ≤ 5860207204053^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863170487 10000000000 5860207204053 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2219603697/5000000000 : ℝ), (6061612833/10000000000 : ℝ), (1863170487/10000000000 : ℝ)] ![(8870546799099/25000000000000 : ℝ), (52797398380971/100000000000000 : ℝ), (5860207204053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2219603697/5000000000 : ℝ)|^37 ≤ (8870546799099/25000000000000 : ℝ)^29
        have hw : |(2219603697/5000000000 : ℝ)|=(2219603697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6061612833/10000000000 : ℝ)|^37 ≤ (52797398380971/100000000000000 : ℝ)^29
        have hw : |(6061612833/10000000000 : ℝ)|=(6061612833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1863170487/10000000000 : ℝ)|^37 ≤ (5860207204053/50000000000000 : ℝ)^29
        have hw : |(1863170487/10000000000 : ℝ)|=(1863170487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s2_s2_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-28720531/1250000000 : ℝ)*x 0 + (2450818107/5000000000 : ℝ)*x 1 + (6606353823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28720531/1250000000 : ℝ)^37 ≤ (81137652589/10000000000000 : ℝ)^29 := by
    have hnat : (28720531 : ℕ)^37*10000000000000^29 ≤ 81137652589^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28720531 1250000000 81137652589 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2450818107/5000000000 : ℝ)^37 ≤ (20132046685741/50000000000000 : ℝ)^29 := by
    have hnat : (2450818107 : ℕ)^37*50000000000000^29 ≤ 20132046685741^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2450818107 5000000000 20132046685741 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6606353823/10000000000 : ℝ)^37 ≤ (14731132523011/25000000000000 : ℝ)^29 := by
    have hnat : (6606353823 : ℕ)^37*25000000000000^29 ≤ 14731132523011^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6606353823 10000000000 14731132523011 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-28720531/1250000000 : ℝ), (2450818107/5000000000 : ℝ), (6606353823/10000000000 : ℝ)] ![(81137652589/10000000000000 : ℝ), (20132046685741/50000000000000 : ℝ), (14731132523011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-28720531/1250000000 : ℝ)|^37 ≤ (81137652589/10000000000000 : ℝ)^29
        have hw : |(-28720531/1250000000 : ℝ)|=(28720531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2450818107/5000000000 : ℝ)|^37 ≤ (20132046685741/50000000000000 : ℝ)^29
        have hw : |(2450818107/5000000000 : ℝ)|=(2450818107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6606353823/10000000000 : ℝ)|^37 ≤ (14731132523011/25000000000000 : ℝ)^29
        have hw : |(6606353823/10000000000 : ℝ)|=(6606353823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s2_s2_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (284001597/625000000 : ℝ)*x 0 + (-443286043/5000000000 : ℝ)*x 1 + (3302166587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (284001597/625000000 : ℝ)^37 ≤ (9138642203733/25000000000000 : ℝ)^29 := by
    have hnat : (284001597 : ℕ)^37*25000000000000^29 ≤ 9138642203733^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284001597 625000000 9138642203733 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443286043/5000000000 : ℝ)^37 ≤ (1135973717833/25000000000000 : ℝ)^29 := by
    have hnat : (443286043 : ℕ)^37*25000000000000^29 ≤ 1135973717833^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443286043 5000000000 1135973717833 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3302166587/5000000000 : ℝ)^37 ≤ (11780307260199/20000000000000 : ℝ)^29 := by
    have hnat : (3302166587 : ℕ)^37*20000000000000^29 ≤ 11780307260199^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3302166587 5000000000 11780307260199 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(284001597/625000000 : ℝ), (-443286043/5000000000 : ℝ), (3302166587/5000000000 : ℝ)] ![(9138642203733/25000000000000 : ℝ), (1135973717833/25000000000000 : ℝ), (11780307260199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(284001597/625000000 : ℝ)|^37 ≤ (9138642203733/25000000000000 : ℝ)^29
        have hw : |(284001597/625000000 : ℝ)|=(284001597/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-443286043/5000000000 : ℝ)|^37 ≤ (1135973717833/25000000000000 : ℝ)^29
        have hw : |(-443286043/5000000000 : ℝ)|=(443286043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3302166587/5000000000 : ℝ)|^37 ≤ (11780307260199/20000000000000 : ℝ)^29
        have hw : |(3302166587/5000000000 : ℝ)|=(3302166587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s2_s2_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3282528419/5000000000 : ℝ)*x 0 + (4966148949/10000000000 : ℝ)*x 1 + (-91105641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3282528419/5000000000 : ℝ)^37 ≤ (58454980806877/100000000000000 : ℝ)^29 := by
    have hnat : (3282528419 : ℕ)^37*100000000000000^29 ≤ 58454980806877^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3282528419 5000000000 58454980806877 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4966148949/10000000000 : ℝ)^37 ≤ (40941440408439/100000000000000 : ℝ)^29 := by
    have hnat : (4966148949 : ℕ)^37*100000000000000^29 ≤ 40941440408439^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4966148949 10000000000 40941440408439 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91105641/5000000000 : ℝ)^37 ≤ (603578772063/100000000000000 : ℝ)^29 := by
    have hnat : (91105641 : ℕ)^37*100000000000000^29 ≤ 603578772063^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91105641 5000000000 603578772063 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3282528419/5000000000 : ℝ), (4966148949/10000000000 : ℝ), (-91105641/5000000000 : ℝ)] ![(58454980806877/100000000000000 : ℝ), (40941440408439/100000000000000 : ℝ), (603578772063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3282528419/5000000000 : ℝ)|^37 ≤ (58454980806877/100000000000000 : ℝ)^29
        have hw : |(3282528419/5000000000 : ℝ)|=(3282528419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4966148949/10000000000 : ℝ)|^37 ≤ (40941440408439/100000000000000 : ℝ)^29
        have hw : |(4966148949/10000000000 : ℝ)|=(4966148949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-91105641/5000000000 : ℝ)|^37 ≤ (603578772063/100000000000000 : ℝ)^29
        have hw : |(-91105641/5000000000 : ℝ)|=(91105641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s2_s2_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (26564469/39062500 : ℝ)*x 0 + (1786880421/5000000000 : ℝ)*x 1 + (945928079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26564469/39062500 : ℝ)^37 ≤ (2445713261371/4000000000000 : ℝ)^29 := by
    have hnat : (26564469 : ℕ)^37*4000000000000^29 ≤ 2445713261371^29*39062500^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26564469 39062500 2445713261371 4000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1786880421/5000000000 : ℝ)^37 ≤ (13453019206833/50000000000000 : ℝ)^29 := by
    have hnat : (1786880421 : ℕ)^37*50000000000000^29 ≤ 13453019206833^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1786880421 5000000000 13453019206833 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945928079/5000000000 : ℝ)^37 ≤ (5975565016221/50000000000000 : ℝ)^29 := by
    have hnat : (945928079 : ℕ)^37*50000000000000^29 ≤ 5975565016221^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945928079 5000000000 5975565016221 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26564469/39062500 : ℝ), (1786880421/5000000000 : ℝ), (945928079/5000000000 : ℝ)] ![(2445713261371/4000000000000 : ℝ), (13453019206833/50000000000000 : ℝ), (5975565016221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26564469/39062500 : ℝ)|^37 ≤ (2445713261371/4000000000000 : ℝ)^29
        have hw : |(26564469/39062500 : ℝ)|=(26564469/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1786880421/5000000000 : ℝ)|^37 ≤ (13453019206833/50000000000000 : ℝ)^29
        have hw : |(1786880421/5000000000 : ℝ)|=(1786880421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(945928079/5000000000 : ℝ)|^37 ≤ (5975565016221/50000000000000 : ℝ)^29
        have hw : |(945928079/5000000000 : ℝ)|=(945928079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s2_s2_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-178715929/10000000000 : ℝ)*x 0 + (6202340953/10000000000 : ℝ)*x 1 + (5352206703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (178715929/10000000000 : ℝ)^37 ≤ (294422779861/50000000000000 : ℝ)^29 := by
    have hnat : (178715929 : ℕ)^37*50000000000000^29 ≤ 294422779861^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178715929 10000000000 294422779861 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6202340953/10000000000 : ℝ)^37 ≤ (543662784481/1000000000000 : ℝ)^29 := by
    have hnat : (6202340953 : ℕ)^37*1000000000000^29 ≤ 543662784481^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6202340953 10000000000 543662784481 1000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5352206703/10000000000 : ℝ)^37 ≤ (4504487598259/10000000000000 : ℝ)^29 := by
    have hnat : (5352206703 : ℕ)^37*10000000000000^29 ≤ 4504487598259^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352206703 10000000000 4504487598259 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-178715929/10000000000 : ℝ), (6202340953/10000000000 : ℝ), (5352206703/10000000000 : ℝ)] ![(294422779861/50000000000000 : ℝ), (543662784481/1000000000000 : ℝ), (4504487598259/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-178715929/10000000000 : ℝ)|^37 ≤ (294422779861/50000000000000 : ℝ)^29
        have hw : |(-178715929/10000000000 : ℝ)|=(178715929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6202340953/10000000000 : ℝ)|^37 ≤ (543662784481/1000000000000 : ℝ)^29
        have hw : |(6202340953/10000000000 : ℝ)|=(6202340953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5352206703/10000000000 : ℝ)|^37 ≤ (4504487598259/10000000000000 : ℝ)^29
        have hw : |(5352206703/10000000000 : ℝ)|=(5352206703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s2_s2_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1643575393/2500000000 : ℝ)*x 0 + (-82872273/5000000000 : ℝ)*x 1 + (496269407/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1643575393/2500000000 : ℝ)^37 ≤ (29280011707229/50000000000000 : ℝ)^29 := by
    have hnat : (1643575393 : ℕ)^37*50000000000000^29 ≤ 29280011707229^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1643575393 2500000000 29280011707229 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82872273/5000000000 : ℝ)^37 ≤ (534872257849/100000000000000 : ℝ)^29 := by
    have hnat : (82872273 : ℕ)^37*100000000000000^29 ≤ 534872257849^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82872273 5000000000 534872257849 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496269407/1000000000 : ℝ)^37 ≤ (8181020862521/20000000000000 : ℝ)^29 := by
    have hnat : (496269407 : ℕ)^37*20000000000000^29 ≤ 8181020862521^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496269407 1000000000 8181020862521 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1643575393/2500000000 : ℝ), (-82872273/5000000000 : ℝ), (496269407/1000000000 : ℝ)] ![(29280011707229/50000000000000 : ℝ), (534872257849/100000000000000 : ℝ), (8181020862521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1643575393/2500000000 : ℝ)|^37 ≤ (29280011707229/50000000000000 : ℝ)^29
        have hw : |(1643575393/2500000000 : ℝ)|=(1643575393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-82872273/5000000000 : ℝ)|^37 ≤ (534872257849/100000000000000 : ℝ)^29
        have hw : |(-82872273/5000000000 : ℝ)|=(82872273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(496269407/1000000000 : ℝ)|^37 ≤ (8181020862521/20000000000000 : ℝ)^29
        have hw : |(496269407/1000000000 : ℝ)|=(496269407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s2_s2_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4516276077/10000000000 : ℝ)*x 0 + (831793189/1250000000 : ℝ)*x 1 + (-842668087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4516276077/10000000000 : ℝ)^37 ≤ (9067499085393/25000000000000 : ℝ)^29 := by
    have hnat : (4516276077 : ℕ)^37*25000000000000^29 ≤ 9067499085393^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516276077 10000000000 9067499085393 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (831793189/1250000000 : ℝ)^37 ≤ (59471216457309/100000000000000 : ℝ)^29 := by
    have hnat : (831793189 : ℕ)^37*100000000000000^29 ≤ 59471216457309^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831793189 1250000000 59471216457309 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (842668087/10000000000 : ℝ)^37 ≤ (2129393595337/50000000000000 : ℝ)^29 := by
    have hnat : (842668087 : ℕ)^37*50000000000000^29 ≤ 2129393595337^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842668087 10000000000 2129393595337 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4516276077/10000000000 : ℝ), (831793189/1250000000 : ℝ), (-842668087/10000000000 : ℝ)] ![(9067499085393/25000000000000 : ℝ), (59471216457309/100000000000000 : ℝ), (2129393595337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4516276077/10000000000 : ℝ)|^37 ≤ (9067499085393/25000000000000 : ℝ)^29
        have hw : |(4516276077/10000000000 : ℝ)|=(4516276077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(831793189/1250000000 : ℝ)|^37 ≤ (59471216457309/100000000000000 : ℝ)^29
        have hw : |(831793189/1250000000 : ℝ)|=(831793189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-842668087/10000000000 : ℝ)|^37 ≤ (2129393595337/50000000000000 : ℝ)^29
        have hw : |(-842668087/10000000000 : ℝ)|=(842668087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s2_s2_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6966718339/10000000000 : ℝ)*x 0 + (2777175719/10000000000 : ℝ)*x 1 + (1272085793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6966718339/10000000000 : ℝ)^37 ≤ (31527948024437/50000000000000 : ℝ)^29 := by
    have hnat : (6966718339 : ℕ)^37*50000000000000^29 ≤ 31527948024437^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6966718339 10000000000 31527948024437 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2777175719/10000000000 : ℝ)^37 ≤ (9751796625847/50000000000000 : ℝ)^29 := by
    have hnat : (2777175719 : ℕ)^37*50000000000000^29 ≤ 9751796625847^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2777175719 10000000000 9751796625847 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1272085793/5000000000 : ℝ)^37 ≤ (4360127669669/25000000000000 : ℝ)^29 := by
    have hnat : (1272085793 : ℕ)^37*25000000000000^29 ≤ 4360127669669^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272085793 5000000000 4360127669669 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6966718339/10000000000 : ℝ), (2777175719/10000000000 : ℝ), (1272085793/5000000000 : ℝ)] ![(31527948024437/50000000000000 : ℝ), (9751796625847/50000000000000 : ℝ), (4360127669669/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6966718339/10000000000 : ℝ)|^37 ≤ (31527948024437/50000000000000 : ℝ)^29
        have hw : |(6966718339/10000000000 : ℝ)|=(6966718339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2777175719/10000000000 : ℝ)|^37 ≤ (9751796625847/50000000000000 : ℝ)^29
        have hw : |(2777175719/10000000000 : ℝ)|=(2777175719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1272085793/5000000000 : ℝ)|^37 ≤ (4360127669669/25000000000000 : ℝ)^29
        have hw : |(1272085793/5000000000 : ℝ)|=(1272085793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313063_s2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((66119/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(66119/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6627/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6627/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6371/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6371/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((48059/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48059/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48877/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48877/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46727/100000 : ℝ)*X 1 2) := by
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
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
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
  have s2_pow0 : (66119/100000 : ℝ) ^ (73/16 : ℝ) ≤ (7571965755772303541/50000000000000000000 : ℝ) := by
    have hpowers : (66119/100000 : ℝ)^73 ≤ (7571965755772303541/50000000000000000000 : ℝ)^16 := by
      have hnat : (66119 : ℕ)^73*50000000000000000000^16 ≤ 7571965755772303541^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66119 100000 7571965755772303541 50000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (66119/100000 : ℝ)) (X := (7571965755772303541/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (57571965755772303541/50000000000000000000 : ℝ) ≤ (5156947393097233/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (57571965755772303541/50000000000000000000 : ℝ)^16 ≤ (5156947393097233/5000000000000000 : ℝ)^73 := by
      have hnat : (57571965755772303541 : ℕ)^16*5000000000000000^73 ≤ 5156947393097233^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57571965755772303541 50000000000000000000 5156947393097233 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5156947393097233/5000000000000000 : ℝ)) (X := (57571965755772303541/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (32571965755772303541/25000000000000000000 : ℝ) ≤ (529851824478801/500000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (32571965755772303541/25000000000000000000 : ℝ)^16 ≤ (529851824478801/500000000000000 : ℝ)^73 := by
      have hnat : (32571965755772303541 : ℕ)^16*500000000000000^73 ≤ 529851824478801^73*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32571965755772303541 25000000000000000000 529851824478801 500000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (529851824478801/500000000000000 : ℝ)) (X := (32571965755772303541/25000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(156947393097233/3305950000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(141570851690777/3305950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (66119/100000 : ℝ)) (alpha := (156947393097233/3305950000000000 : ℝ)) (beta := (141570851690777/3305950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (66119/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(156947393097233/3305950000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(141570851690777/3305950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (6627/10000 : ℝ) ^ (73/16 : ℝ) ≤ (1912796160359079293/12500000000000000000 : ℝ) := by
    have hpowers : (6627/10000 : ℝ)^73 ≤ (1912796160359079293/12500000000000000000 : ℝ)^16 := by
      have hnat : (6627 : ℕ)^73*12500000000000000000^16 ≤ 1912796160359079293^16*10000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6627 10000 1912796160359079293 12500000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6627/10000 : ℝ)) (X := (1912796160359079293/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (14412796160359079293/12500000000000000000 : ℝ) ≤ (2063400733745497/2000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (14412796160359079293/12500000000000000000 : ℝ)^16 ≤ (2063400733745497/2000000000000000 : ℝ)^73 := by
      have hnat : (14412796160359079293 : ℕ)^16*2000000000000000^73 ≤ 2063400733745497^73*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14412796160359079293 12500000000000000000 2063400733745497 2000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2063400733745497/2000000000000000 : ℝ)) (X := (14412796160359079293/12500000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (8162796160359079293/6250000000000000000 : ℝ) ≤ (10602680065045419/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (8162796160359079293/6250000000000000000 : ℝ)^16 ≤ (10602680065045419/10000000000000000 : ℝ)^73 := by
      have hnat : (8162796160359079293 : ℕ)^16*10000000000000000^73 ≤ 10602680065045419^73*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8162796160359079293 6250000000000000000 10602680065045419 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10602680065045419/10000000000000000 : ℝ)) (X := (8162796160359079293/6250000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(63400733745497/1325400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(142838198158967/3313500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (6627/10000 : ℝ)) (alpha := (63400733745497/1325400000000000 : ℝ)) (beta := (142838198158967/3313500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (6627/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(63400733745497/1325400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(142838198158967/3313500000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (6371/10000 : ℝ) ^ (73/16 : ℝ) ≤ (6392447979709257849/50000000000000000000 : ℝ) := by
    have hpowers : (6371/10000 : ℝ)^73 ≤ (6392447979709257849/50000000000000000000 : ℝ)^16 := by
      have hnat : (6371 : ℕ)^73*50000000000000000000^16 ≤ 6392447979709257849^16*10000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6371 10000 6392447979709257849 50000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6371/10000 : ℝ)) (X := (6392447979709257849/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (56392447979709257849/50000000000000000000 : ℝ) ≤ (320850177004627/312500000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (56392447979709257849/50000000000000000000 : ℝ)^16 ≤ (320850177004627/312500000000000 : ℝ)^73 := by
      have hnat : (56392447979709257849 : ℕ)^16*312500000000000^73 ≤ 320850177004627^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56392447979709257849 50000000000000000000 320850177004627 312500000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (320850177004627/312500000000000 : ℝ)) (X := (56392447979709257849/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (31392447979709257849/25000000000000000000 : ℝ) ≤ (2627928056571503/2500000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (31392447979709257849/25000000000000000000 : ℝ)^16 ≤ (2627928056571503/2500000000000000 : ℝ)^73 := by
      have hnat : (31392447979709257849 : ℕ)^16*2500000000000000^73 ≤ 2627928056571503^73*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31392447979709257849 25000000000000000000 2627928056571503 2500000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2627928056571503/2500000000000000 : ℝ)) (X := (31392447979709257849/25000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(8350177004627/199093750000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(61126640534487/1592750000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (6371/10000 : ℝ)) (alpha := (8350177004627/199093750000000 : ℝ)) (beta := (61126640534487/1592750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (6371/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(8350177004627/199093750000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(61126640534487/1592750000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-570796423/5000000000 : ℝ)*X 0 0+(5482145693/10000000000 : ℝ)*X 0 1+(2779709293/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((685295553/1250000000 : ℝ)*X 1 0+(-1144322099/10000000000 : ℝ)*X 1 1+(1111487297/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((2761684563/5000000000 : ℝ)*X 2 0+(1386356333/2500000000 : ℝ)*X 2 1+(-1099406851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((268928269/625000000 : ℝ)*X 0 0+(2121499291/5000000000 : ℝ)*X 0 1+(1033726203/2500000000 : ℝ)*X 0 2+(268928269/625000000 : ℝ)*X 1 0+(2121499291/5000000000 : ℝ)*X 1 1+(1033726203/2500000000 : ℝ)*X 1 2+(268928269/625000000 : ℝ)*X 2 0+(2121499291/5000000000 : ℝ)*X 2 1+(1033726203/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-907813849/10000000000 : ℝ)*X 0 0+(56435869/125000000 : ℝ)*X 0 1+(6618357241/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((4885091733/10000000000 : ℝ)*X 1 0+(-9716407/400000000 : ℝ)*X 1 1+(1654084069/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4613814407/10000000000 : ℝ)*X 2 0+(689026037/1000000000 : ℝ)*X 2 1+(-170207503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((2219603697/5000000000 : ℝ)*X 0 0+(6061612833/10000000000 : ℝ)*X 0 1+(1863170487/10000000000 : ℝ)*X 0 2+(2219603697/5000000000 : ℝ)*X 1 0+(6061612833/10000000000 : ℝ)*X 1 1+(1863170487/10000000000 : ℝ)*X 1 2+(2219603697/5000000000 : ℝ)*X 2 0+(6061612833/10000000000 : ℝ)*X 2 1+(1863170487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-28720531/1250000000 : ℝ)*X 0 0+(2450818107/5000000000 : ℝ)*X 0 1+(6606353823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((284001597/625000000 : ℝ)*X 1 0+(-443286043/5000000000 : ℝ)*X 1 1+(3302166587/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((3282528419/5000000000 : ℝ)*X 2 0+(4966148949/10000000000 : ℝ)*X 2 1+(-91105641/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((26564469/39062500 : ℝ)*X 0 0+(1786880421/5000000000 : ℝ)*X 0 1+(945928079/5000000000 : ℝ)*X 0 2+(26564469/39062500 : ℝ)*X 1 0+(1786880421/5000000000 : ℝ)*X 1 1+(945928079/5000000000 : ℝ)*X 1 2+(26564469/39062500 : ℝ)*X 2 0+(1786880421/5000000000 : ℝ)*X 2 1+(945928079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-178715929/10000000000 : ℝ)*X 0 0+(6202340953/10000000000 : ℝ)*X 0 1+(5352206703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1643575393/2500000000 : ℝ)*X 1 0+(-82872273/5000000000 : ℝ)*X 1 1+(496269407/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4516276077/10000000000 : ℝ)*X 2 0+(831793189/1250000000 : ℝ)*X 2 1+(-842668087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((6966718339/10000000000 : ℝ)*X 0 0+(2777175719/10000000000 : ℝ)*X 0 1+(1272085793/5000000000 : ℝ)*X 0 2+(6966718339/10000000000 : ℝ)*X 1 0+(2777175719/10000000000 : ℝ)*X 1 1+(1272085793/5000000000 : ℝ)*X 1 2+(6966718339/10000000000 : ℝ)*X 2 0+(2777175719/10000000000 : ℝ)*X 2 1+(1272085793/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((48059/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48059/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2626831800180515604537/398187500000000000000000000 : ℝ) := by norm_num
    linear_combination (4498643/1000000000000 : ℝ)*(base23) + (3917862193/25000000000 : ℝ)*(base60) + (3550055409909/1000000000000 : ℝ)*(major_s2_0) + (3550055409909/1000000000000 : ℝ)*(major_s2_1) + (3550055409909/1000000000000 : ℝ)*(major_s2_2) + (868649/500000000000 : ℝ)*(sp_s2_0) + (7535321/1000000000000 : ℝ)*(sp_s2_6) + (5005496603393/1000000000000 : ℝ)*(sp_s2_7) + (5005486542017/1000000000000 : ℝ)*(sp_s2_8) + (5005488064227/1000000000000 : ℝ)*(sp_s2_9) + (1047290541021/500000000000 : ℝ)*(sp_s2_13) + (1353923/62500000000 : ℝ)*(sp_s2_14) + (16730721/500000000000 : ℝ)*(sp_s2_15) + (27440589/1000000000000 : ℝ)*(sp_s2_23) + (1047294308681/500000000000 : ℝ)*(f.failure) + (5005520003459/1000000000000 : ℝ)*(f.sum) + (1251689536880882611/14073539000000000000000000000000 : ℝ)*base62 + (443310942108667/1592750000000000000000000000 : ℝ)*base64 + (253342216228051/1104500000000000000000000000 : ℝ)*base67 + (423944763064869/1592750000000000000000000000 : ℝ)*base69 + (67135875105925466513/105311037250000000000000000000000 : ℝ)*base70 + (720974293629223/3305950000000000000000000000 : ℝ)*base73 + (17254349463271/441800000000000000000000000 : ℝ)*base75 + (105861882334027/3305950000000000000000000000 : ℝ)*base77 + (14501324869746460611/73028435500000000000000000000000 : ℝ)*base78 + (33353/50000000000000000 : ℝ)*base86 + (33353/50000000000000000 : ℝ)*base88 + (33353/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48877/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48877/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3104458009918985530338188831761/232632081285250000000000000000000000 : ℝ) := by norm_num
    linear_combination (3884407/500000000000 : ℝ)*(base21) + (9959/500000000000 : ℝ)*(base49) + (2253/15625000000 : ℝ)*(base60) + (895841768383/250000000000 : ℝ)*(major_s2_0) + (895841768383/250000000000 : ℝ)*(major_s2_1) + (895841768383/250000000000 : ℝ)*(major_s2_2) + (32509261/1000000000000 : ℝ)*(sp_s2_2) + (5310073/100000000000 : ℝ)*(sp_s2_7) + (45916027/1000000000000 : ℝ)*(sp_s2_8) + (5052433574347/1000000000000 : ℝ)*(sp_s2_14) + (101048815181/20000000000 : ℝ)*(sp_s2_15) + (5052446397003/1000000000000 : ℝ)*(sp_s2_16) + (2114199944547/1000000000000 : ℝ)*(sp_s2_20) + (21539563/500000000000 : ℝ)*(sp_s2_27) + (2114243023673/1000000000000 : ℝ)*(f.failure) + (5052486675077/1000000000000 : ℝ)*(f.sum) + (2905734819455478329/10555154250000000000000000000000 : ℝ)*base63 + (509801714896533/796375000000000000000000000 : ℝ)*base64 + (197206981613947/1656750000000000000000000000 : ℝ)*base67 + (269593974087437/1592750000000000000000000000 : ℝ)*base69 + (56180992806205008299/105311037250000000000000000000000 : ℝ)*base70 + (223904974515983/1652975000000000000000000000 : ℝ)*base72 + (308360782826119/331350000000000000000000000 : ℝ)*base74 + (1875965944324909/3305950000000000000000000000 : ℝ)*base76 + (17732443355091359933/109542653250000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (65751/100000000000000000 : ℝ)*base87 + (65751/100000000000000000 : ℝ)*base89 + (65751/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46727/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1486815127869459257922590008961/465264162570500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2013857/1000000000000 : ℝ)*(base15) + (23066982587/125000000000 : ℝ)*(base40) + (3377555859443/1000000000000 : ℝ)*(major_s2_0) + (3377555859443/1000000000000 : ℝ)*(major_s2_1) + (3377555859443/1000000000000 : ℝ)*(major_s2_2) + (7183791/500000000000 : ℝ)*(sp_s2_0) + (12365523/1000000000000 : ℝ)*(sp_s2_1) + (1409629/200000000000 : ℝ)*(sp_s2_2) + (13319571/1000000000000 : ℝ)*(sp_s2_9) + (5372769/250000000000 : ℝ)*(sp_s2_20) + (1190571280239/250000000000 : ℝ)*(sp_s2_21) + (4762285109159/1000000000000 : ℝ)*(sp_s2_22) + (2381139560411/500000000000 : ℝ)*(sp_s2_23) + (996394837027/500000000000 : ℝ)*(sp_s2_27) + (199281116513/100000000000 : ℝ)*(f.failure) + (4762299488539/1000000000000 : ℝ)*(f.sum) + (15011555201258879891/42220617000000000000000000000000 : ℝ)*base62 + (146137509944441/1592750000000000000000000000 : ℝ)*base65 + (365139201573181/3313500000000000000000000000 : ℝ)*base67 + (537720839463581/796375000000000000000000000 : ℝ)*base68 + (21439312131807505151/105311037250000000000000000000000 : ℝ)*base70 + (258490114641951/826487500000000000000000000 : ℝ)*base72 + (173506903284569/1325400000000000000000000000 : ℝ)*base74 + (61704674116479/3305950000000000000000000000 : ℝ)*base77 + (13219462102965005191/219085306500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (8831/10000000000000000 : ℝ)*base87 + (8831/10000000000000000 : ℝ)*base89 + (8831/10000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((66119/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(66119/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6627/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6627/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6371/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6371/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((48059/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48059/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48877/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48877/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46727/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313063_s2 p hpa hpb X hX hprev1

#print axioms solution

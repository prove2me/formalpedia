-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306080_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:59:45.199561+00:00
-- url     : https://prove2.me/submissions/7e63c033-c140-471e-a5fd-578397f4ce88

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
theorem collision_support_c306080_s1_s1_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3251942149/10000000000 : ℝ)*x 0 + (582407949/1000000000 : ℝ)*x 1 + (188402481/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3251942149/10000000000 : ℝ)^135 ≤ (5734763833659/25000000000000 : ℝ)^103 := by
    have hnat : (3251942149 : ℕ)^135*25000000000000^103 ≤ 5734763833659^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3251942149 10000000000 5734763833659 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (582407949/1000000000 : ℝ)^135 ≤ (24618308233637/50000000000000 : ℝ)^103 := by
    have hnat : (582407949 : ℕ)^135*50000000000000^103 ≤ 24618308233637^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582407949 1000000000 24618308233637 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188402481/500000000 : ℝ)^135 ≤ (13912164095017/50000000000000 : ℝ)^103 := by
    have hnat : (188402481 : ℕ)^135*50000000000000^103 ≤ 13912164095017^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188402481 500000000 13912164095017 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3251942149/10000000000 : ℝ), (582407949/1000000000 : ℝ), (188402481/500000000 : ℝ)] ![(5734763833659/25000000000000 : ℝ), (24618308233637/50000000000000 : ℝ), (13912164095017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3251942149/10000000000 : ℝ)|^135 ≤ (5734763833659/25000000000000 : ℝ)^103
        have hw : |(-3251942149/10000000000 : ℝ)|=(3251942149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(582407949/1000000000 : ℝ)|^135 ≤ (24618308233637/50000000000000 : ℝ)^103
        have hw : |(582407949/1000000000 : ℝ)|=(582407949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(188402481/500000000 : ℝ)|^135 ≤ (13912164095017/50000000000000 : ℝ)^103
        have hw : |(188402481/500000000 : ℝ)|=(188402481/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306080_s1_s1_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (716544929/2500000000 : ℝ)*x 0 + (6510635511/10000000000 : ℝ)*x 1 + (-830265953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (716544929/2500000000 : ℝ)^135 ≤ (2430013396771/12500000000000 : ℝ)^103 := by
    have hnat : (716544929 : ℕ)^135*12500000000000^103 ≤ 2430013396771^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      716544929 2500000000 2430013396771 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6510635511/10000000000 : ℝ)^135 ≤ (28489837484231/50000000000000 : ℝ)^103 := by
    have hnat : (6510635511 : ℕ)^135*50000000000000^103 ≤ 28489837484231^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6510635511 10000000000 28489837484231 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830265953/2500000000 : ℝ)^135 ≤ (5895054462521/25000000000000 : ℝ)^103 := by
    have hnat : (830265953 : ℕ)^135*25000000000000^103 ≤ 5895054462521^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830265953 2500000000 5895054462521 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(716544929/2500000000 : ℝ), (6510635511/10000000000 : ℝ), (-830265953/2500000000 : ℝ)] ![(2430013396771/12500000000000 : ℝ), (28489837484231/50000000000000 : ℝ), (5895054462521/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(716544929/2500000000 : ℝ)|^135 ≤ (2430013396771/12500000000000 : ℝ)^103
        have hw : |(716544929/2500000000 : ℝ)|=(716544929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6510635511/10000000000 : ℝ)|^135 ≤ (28489837484231/50000000000000 : ℝ)^103
        have hw : |(6510635511/10000000000 : ℝ)|=(6510635511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-830265953/2500000000 : ℝ)|^135 ≤ (5895054462521/25000000000000 : ℝ)^103
        have hw : |(-830265953/2500000000 : ℝ)|=(830265953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306080_s1_s1_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4440367771/10000000000 : ℝ)*x 0 + (4596821487/10000000000 : ℝ)*x 1 + (3928594347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4440367771/10000000000 : ℝ)^135 ≤ (539137104137/1562500000000 : ℝ)^103 := by
    have hnat : (4440367771 : ℕ)^135*1562500000000^103 ≤ 539137104137^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4440367771 10000000000 539137104137 1562500000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4596821487/10000000000 : ℝ)^135 ≤ (7221378433403/20000000000000 : ℝ)^103 := by
    have hnat : (4596821487 : ℕ)^135*20000000000000^103 ≤ 7221378433403^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4596821487 10000000000 7221378433403 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3928594347/10000000000 : ℝ)^135 ≤ (1836770821553/6250000000000 : ℝ)^103 := by
    have hnat : (3928594347 : ℕ)^135*6250000000000^103 ≤ 1836770821553^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3928594347 10000000000 1836770821553 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4440367771/10000000000 : ℝ), (4596821487/10000000000 : ℝ), (3928594347/10000000000 : ℝ)] ![(539137104137/1562500000000 : ℝ), (7221378433403/20000000000000 : ℝ), (1836770821553/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4440367771/10000000000 : ℝ)|^135 ≤ (539137104137/1562500000000 : ℝ)^103
        have hw : |(4440367771/10000000000 : ℝ)|=(4440367771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4596821487/10000000000 : ℝ)|^135 ≤ (7221378433403/20000000000000 : ℝ)^103
        have hw : |(4596821487/10000000000 : ℝ)|=(4596821487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3928594347/10000000000 : ℝ)|^135 ≤ (1836770821553/6250000000000 : ℝ)^103
        have hw : |(3928594347/10000000000 : ℝ)|=(3928594347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306080_s1_s1_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-448969521/1250000000 : ℝ)*x 0 + (3885682203/10000000000 : ℝ)*x 1 + (33928507/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448969521/1250000000 : ℝ)^135 ≤ (6532655535253/25000000000000 : ℝ)^103 := by
    have hnat : (448969521 : ℕ)^135*25000000000000^103 ≤ 6532655535253^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448969521 1250000000 6532655535253 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3885682203/10000000000 : ℝ)^135 ≤ (7242077037651/25000000000000 : ℝ)^103 := by
    have hnat : (3885682203 : ℕ)^135*25000000000000^103 ≤ 7242077037651^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3885682203 10000000000 7242077037651 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33928507/62500000 : ℝ)^135 ≤ (11225267422569/25000000000000 : ℝ)^103 := by
    have hnat : (33928507 : ℕ)^135*25000000000000^103 ≤ 11225267422569^103*62500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33928507 62500000 11225267422569 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-448969521/1250000000 : ℝ), (3885682203/10000000000 : ℝ), (33928507/62500000 : ℝ)] ![(6532655535253/25000000000000 : ℝ), (7242077037651/25000000000000 : ℝ), (11225267422569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-448969521/1250000000 : ℝ)|^135 ≤ (6532655535253/25000000000000 : ℝ)^103
        have hw : |(-448969521/1250000000 : ℝ)|=(448969521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3885682203/10000000000 : ℝ)|^135 ≤ (7242077037651/25000000000000 : ℝ)^103
        have hw : |(3885682203/10000000000 : ℝ)|=(3885682203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33928507/62500000 : ℝ)|^135 ≤ (11225267422569/25000000000000 : ℝ)^103
        have hw : |(33928507/62500000 : ℝ)|=(33928507/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306080_s1_s1_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (19589697/40000000 : ℝ)*x 0 + (62479937/5000000000 : ℝ)*x 1 + (851349637/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19589697/40000000 : ℝ)^135 ≤ (19616296878393/50000000000000 : ℝ)^103 := by
    have hnat : (19589697 : ℕ)^135*50000000000000^103 ≤ 19616296878393^103*40000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19589697 40000000 19616296878393 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62479937/5000000000 : ℝ)^135 ≤ (320240312659/100000000000000 : ℝ)^103 := by
    have hnat : (62479937 : ℕ)^135*100000000000000^103 ≤ 320240312659^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62479937 5000000000 320240312659 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (851349637/1250000000 : ℝ)^135 ≤ (30223582957561/50000000000000 : ℝ)^103 := by
    have hnat : (851349637 : ℕ)^135*50000000000000^103 ≤ 30223582957561^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851349637 1250000000 30223582957561 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(19589697/40000000 : ℝ), (62479937/5000000000 : ℝ), (851349637/1250000000 : ℝ)] ![(19616296878393/50000000000000 : ℝ), (320240312659/100000000000000 : ℝ), (30223582957561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(19589697/40000000 : ℝ)|^135 ≤ (19616296878393/50000000000000 : ℝ)^103
        have hw : |(19589697/40000000 : ℝ)|=(19589697/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(62479937/5000000000 : ℝ)|^135 ≤ (320240312659/100000000000000 : ℝ)^103
        have hw : |(62479937/5000000000 : ℝ)|=(62479937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(851349637/1250000000 : ℝ)|^135 ≤ (30223582957561/50000000000000 : ℝ)^103
        have hw : |(851349637/1250000000 : ℝ)|=(851349637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306080_s1_s1_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (273262181/2500000000 : ℝ)*x 0 + (4078175957/5000000000 : ℝ)*x 1 + (-2696466179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273262181/2500000000 : ℝ)^135 ≤ (5494958559371/100000000000000 : ℝ)^103 := by
    have hnat : (273262181 : ℕ)^135*100000000000000^103 ≤ 5494958559371^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273262181 2500000000 5494958559371 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4078175957/5000000000 : ℝ)^135 ≤ (76559581968043/100000000000000 : ℝ)^103 := by
    have hnat : (4078175957 : ℕ)^135*100000000000000^103 ≤ 76559581968043^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4078175957 5000000000 76559581968043 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696466179/10000000000 : ℝ)^135 ≤ (8972729729047/50000000000000 : ℝ)^103 := by
    have hnat : (2696466179 : ℕ)^135*50000000000000^103 ≤ 8972729729047^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696466179 10000000000 8972729729047 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273262181/2500000000 : ℝ), (4078175957/5000000000 : ℝ), (-2696466179/10000000000 : ℝ)] ![(5494958559371/100000000000000 : ℝ), (76559581968043/100000000000000 : ℝ), (8972729729047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273262181/2500000000 : ℝ)|^135 ≤ (5494958559371/100000000000000 : ℝ)^103
        have hw : |(273262181/2500000000 : ℝ)|=(273262181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4078175957/5000000000 : ℝ)|^135 ≤ (76559581968043/100000000000000 : ℝ)^103
        have hw : |(4078175957/5000000000 : ℝ)|=(4078175957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2696466179/10000000000 : ℝ)|^135 ≤ (8972729729047/50000000000000 : ℝ)^103
        have hw : |(-2696466179/10000000000 : ℝ)|=(2696466179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306080_s1_s1_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (573184801/2000000000 : ℝ)*x 0 + (815657253/1250000000 : ℝ)*x 1 + (3303263087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (573184801/2000000000 : ℝ)^135 ≤ (4859458496781/25000000000000 : ℝ)^103 := by
    have hnat : (573184801 : ℕ)^135*25000000000000^103 ≤ 4859458496781^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573184801 2000000000 4859458496781 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (815657253/1250000000 : ℝ)^135 ≤ (57147465155757/100000000000000 : ℝ)^103 := by
    have hnat : (815657253 : ℕ)^135*100000000000000^103 ≤ 57147465155757^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      815657253 1250000000 57147465155757 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3303263087/10000000000 : ℝ)^135 ≤ (731709401271/3125000000000 : ℝ)^103 := by
    have hnat : (3303263087 : ℕ)^135*3125000000000^103 ≤ 731709401271^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3303263087 10000000000 731709401271 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(573184801/2000000000 : ℝ), (815657253/1250000000 : ℝ), (3303263087/10000000000 : ℝ)] ![(4859458496781/25000000000000 : ℝ), (57147465155757/100000000000000 : ℝ), (731709401271/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(573184801/2000000000 : ℝ)|^135 ≤ (4859458496781/25000000000000 : ℝ)^103
        have hw : |(573184801/2000000000 : ℝ)|=(573184801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(815657253/1250000000 : ℝ)|^135 ≤ (57147465155757/100000000000000 : ℝ)^103
        have hw : |(815657253/1250000000 : ℝ)|=(815657253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3303263087/10000000000 : ℝ)|^135 ≤ (731709401271/3125000000000 : ℝ)^103
        have hw : |(3303263087/10000000000 : ℝ)|=(3303263087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306080_s1_s1_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-5501846109/10000000000 : ℝ)*x 0 + (1360628683/2500000000 : ℝ)*x 1 + (1626366097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5501846109/10000000000 : ℝ)^135 ≤ (45697211654047/100000000000000 : ℝ)^103 := by
    have hnat : (5501846109 : ℕ)^135*100000000000000^103 ≤ 45697211654047^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501846109 10000000000 45697211654047 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360628683/2500000000 : ℝ)^135 ≤ (5631550108547/12500000000000 : ℝ)^103 := by
    have hnat : (1360628683 : ℕ)^135*12500000000000^103 ≤ 5631550108547^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360628683 2500000000 5631550108547 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1626366097/10000000000 : ℝ)^135 ≤ (9250387464897/100000000000000 : ℝ)^103 := by
    have hnat : (1626366097 : ℕ)^135*100000000000000^103 ≤ 9250387464897^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1626366097 10000000000 9250387464897 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5501846109/10000000000 : ℝ), (1360628683/2500000000 : ℝ), (1626366097/10000000000 : ℝ)] ![(45697211654047/100000000000000 : ℝ), (5631550108547/12500000000000 : ℝ), (9250387464897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5501846109/10000000000 : ℝ)|^135 ≤ (45697211654047/100000000000000 : ℝ)^103
        have hw : |(-5501846109/10000000000 : ℝ)|=(5501846109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360628683/2500000000 : ℝ)|^135 ≤ (5631550108547/12500000000000 : ℝ)^103
        have hw : |(1360628683/2500000000 : ℝ)|=(1360628683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1626366097/10000000000 : ℝ)|^135 ≤ (9250387464897/100000000000000 : ℝ)^103
        have hw : |(1626366097/10000000000 : ℝ)|=(1626366097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306080_s1_s1_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (351002961/625000000 : ℝ)*x 0 + (1657173/125000000 : ℝ)*x 1 + (6134959087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351002961/625000000 : ℝ)^135 ≤ (46944423432079/100000000000000 : ℝ)^103 := by
    have hnat : (351002961 : ℕ)^135*100000000000000^103 ≤ 46944423432079^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351002961 625000000 46944423432079 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1657173/125000000 : ℝ)^135 ≤ (69210782757/20000000000000 : ℝ)^103 := by
    have hnat : (1657173 : ℕ)^135*20000000000000^103 ≤ 69210782757^103*125000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1657173 125000000 69210782757 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6134959087/10000000000 : ℝ)^135 ≤ (6588690330899/12500000000000 : ℝ)^103 := by
    have hnat : (6134959087 : ℕ)^135*12500000000000^103 ≤ 6588690330899^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6134959087 10000000000 6588690330899 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(351002961/625000000 : ℝ), (1657173/125000000 : ℝ), (6134959087/10000000000 : ℝ)] ![(46944423432079/100000000000000 : ℝ), (69210782757/20000000000000 : ℝ), (6588690330899/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(351002961/625000000 : ℝ)|^135 ≤ (46944423432079/100000000000000 : ℝ)^103
        have hw : |(351002961/625000000 : ℝ)|=(351002961/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1657173/125000000 : ℝ)|^135 ≤ (69210782757/20000000000000 : ℝ)^103
        have hw : |(1657173/125000000 : ℝ)|=(1657173/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6134959087/10000000000 : ℝ)|^135 ≤ (6588690330899/12500000000000 : ℝ)^103
        have hw : |(6134959087/10000000000 : ℝ)|=(6134959087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306080_s1_s1_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1236804241/10000000000 : ℝ)*x 0 + (5608552759/10000000000 : ℝ)*x 1 + (-5591594933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1236804241/10000000000 : ℝ)^135 ≤ (6460964909447/100000000000000 : ℝ)^103 := by
    have hnat : (1236804241 : ℕ)^135*100000000000000^103 ≤ 6460964909447^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1236804241 10000000000 6460964909447 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5608552759/10000000000 : ℝ)^135 ≤ (46862329857267/100000000000000 : ℝ)^103 := by
    have hnat : (5608552759 : ℕ)^135*100000000000000^103 ≤ 46862329857267^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5608552759 10000000000 46862329857267 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5591594933/10000000000 : ℝ)^135 ≤ (46676705220737/100000000000000 : ℝ)^103 := by
    have hnat : (5591594933 : ℕ)^135*100000000000000^103 ≤ 46676705220737^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591594933 10000000000 46676705220737 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1236804241/10000000000 : ℝ), (5608552759/10000000000 : ℝ), (-5591594933/10000000000 : ℝ)] ![(6460964909447/100000000000000 : ℝ), (46862329857267/100000000000000 : ℝ), (46676705220737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1236804241/10000000000 : ℝ)|^135 ≤ (6460964909447/100000000000000 : ℝ)^103
        have hw : |(1236804241/10000000000 : ℝ)|=(1236804241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5608552759/10000000000 : ℝ)|^135 ≤ (46862329857267/100000000000000 : ℝ)^103
        have hw : |(5608552759/10000000000 : ℝ)|=(5608552759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5591594933/10000000000 : ℝ)|^135 ≤ (46676705220737/100000000000000 : ℝ)^103
        have hw : |(-5591594933/10000000000 : ℝ)|=(5591594933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306080_s1_s1_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (351002961/625000000 : ℝ)*x 0 + (135497707/312500000 : ℝ)*x 1 + (288534023/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351002961/625000000 : ℝ)^135 ≤ (46944423432079/100000000000000 : ℝ)^103 := by
    have hnat : (351002961 : ℕ)^135*100000000000000^103 ≤ 46944423432079^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351002961 625000000 46944423432079 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135497707/312500000 : ℝ)^135 ≤ (16722479860001/50000000000000 : ℝ)^103 := by
    have hnat : (135497707 : ℕ)^135*50000000000000^103 ≤ 16722479860001^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135497707 312500000 16722479860001 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (288534023/1000000000 : ℝ)^135 ≤ (784424673639/4000000000000 : ℝ)^103 := by
    have hnat : (288534023 : ℕ)^135*4000000000000^103 ≤ 784424673639^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288534023 1000000000 784424673639 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(351002961/625000000 : ℝ), (135497707/312500000 : ℝ), (288534023/1000000000 : ℝ)] ![(46944423432079/100000000000000 : ℝ), (16722479860001/50000000000000 : ℝ), (784424673639/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(351002961/625000000 : ℝ)|^135 ≤ (46944423432079/100000000000000 : ℝ)^103
        have hw : |(351002961/625000000 : ℝ)|=(351002961/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135497707/312500000 : ℝ)|^135 ≤ (16722479860001/50000000000000 : ℝ)^103
        have hw : |(135497707/312500000 : ℝ)|=(135497707/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(288534023/1000000000 : ℝ)|^135 ≤ (784424673639/4000000000000 : ℝ)^103
        have hw : |(288534023/1000000000 : ℝ)|=(288534023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306080_s1_s1_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2474121041/10000000000 : ℝ)*x 0 + (3520956551/5000000000 : ℝ)*x 1 + (3020020811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2474121041/10000000000 : ℝ)^135 ≤ (3206263362551/20000000000000 : ℝ)^103 := by
    have hnat : (2474121041 : ℕ)^135*20000000000000^103 ≤ 3206263362551^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2474121041 10000000000 3206263362551 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3520956551/5000000000 : ℝ)^135 ≤ (63149694716817/100000000000000 : ℝ)^103 := by
    have hnat : (3520956551 : ℕ)^135*100000000000000^103 ≤ 63149694716817^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3520956551 5000000000 63149694716817 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3020020811/10000000000 : ℝ)^135 ≤ (1301186778743/6250000000000 : ℝ)^103 := by
    have hnat : (3020020811 : ℕ)^135*6250000000000^103 ≤ 1301186778743^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3020020811 10000000000 1301186778743 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2474121041/10000000000 : ℝ), (3520956551/5000000000 : ℝ), (3020020811/10000000000 : ℝ)] ![(3206263362551/20000000000000 : ℝ), (63149694716817/100000000000000 : ℝ), (1301186778743/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2474121041/10000000000 : ℝ)|^135 ≤ (3206263362551/20000000000000 : ℝ)^103
        have hw : |(-2474121041/10000000000 : ℝ)|=(2474121041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3520956551/5000000000 : ℝ)|^135 ≤ (63149694716817/100000000000000 : ℝ)^103
        have hw : |(3520956551/5000000000 : ℝ)|=(3520956551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3020020811/10000000000 : ℝ)|^135 ≤ (1301186778743/6250000000000 : ℝ)^103
        have hw : |(3020020811/10000000000 : ℝ)|=(3020020811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306080_s1_s1_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7972035111/10000000000 : ℝ)*x 0 + (3454357/5000000000 : ℝ)*x 1 + (443218711/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7972035111/10000000000 : ℝ)^135 ≤ (14859998192303/20000000000000 : ℝ)^103 := by
    have hnat : (7972035111 : ℕ)^135*20000000000000^103 ≤ 14859998192303^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7972035111 10000000000 14859998192303 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3454357/5000000000 : ℝ)^135 ≤ (7202153423/100000000000000 : ℝ)^103 := by
    have hnat : (3454357 : ℕ)^135*100000000000000^103 ≤ 7202153423^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3454357 5000000000 7202153423 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443218711/1250000000 : ℝ)^135 ≤ (12846403437687/50000000000000 : ℝ)^103 := by
    have hnat : (443218711 : ℕ)^135*50000000000000^103 ≤ 12846403437687^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443218711 1250000000 12846403437687 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7972035111/10000000000 : ℝ), (3454357/5000000000 : ℝ), (443218711/1250000000 : ℝ)] ![(14859998192303/20000000000000 : ℝ), (7202153423/100000000000000 : ℝ), (12846403437687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7972035111/10000000000 : ℝ)|^135 ≤ (14859998192303/20000000000000 : ℝ)^103
        have hw : |(7972035111/10000000000 : ℝ)|=(7972035111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3454357/5000000000 : ℝ)|^135 ≤ (7202153423/100000000000000 : ℝ)^103
        have hw : |(3454357/5000000000 : ℝ)|=(3454357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(443218711/1250000000 : ℝ)|^135 ≤ (12846403437687/50000000000000 : ℝ)^103
        have hw : |(443218711/1250000000 : ℝ)|=(443218711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306080_s1_s1_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (537244133/5000000000 : ℝ)*x 0 + (506337621/625000000 : ℝ)*x 1 + (-696849267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537244133/5000000000 : ℝ)^135 ≤ (1343246751887/25000000000000 : ℝ)^103 := by
    have hnat : (537244133 : ℕ)^135*25000000000000^103 ≤ 1343246751887^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537244133 5000000000 1343246751887 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506337621/625000000 : ℝ)^135 ≤ (75884257919731/100000000000000 : ℝ)^103 := by
    have hnat : (506337621 : ℕ)^135*100000000000000^103 ≤ 75884257919731^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506337621 625000000 75884257919731 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (696849267/2500000000 : ℝ)^135 ≤ (4685688764623/25000000000000 : ℝ)^103 := by
    have hnat : (696849267 : ℕ)^135*25000000000000^103 ≤ 4685688764623^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696849267 2500000000 4685688764623 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537244133/5000000000 : ℝ), (506337621/625000000 : ℝ), (-696849267/2500000000 : ℝ)] ![(1343246751887/25000000000000 : ℝ), (75884257919731/100000000000000 : ℝ), (4685688764623/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537244133/5000000000 : ℝ)|^135 ≤ (1343246751887/25000000000000 : ℝ)^103
        have hw : |(537244133/5000000000 : ℝ)|=(537244133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506337621/625000000 : ℝ)|^135 ≤ (75884257919731/100000000000000 : ℝ)^103
        have hw : |(506337621/625000000 : ℝ)|=(506337621/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-696849267/2500000000 : ℝ)|^135 ≤ (4685688764623/25000000000000 : ℝ)^103
        have hw : |(-696849267/2500000000 : ℝ)|=(696849267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306080_s1_s1_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6951711341/10000000000 : ℝ)*x 0 + (3197218181/10000000000 : ℝ)*x 1 + (2408219491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6951711341/10000000000 : ℝ)^135 ≤ (6209159992629/10000000000000 : ℝ)^103 := by
    have hnat : (6951711341 : ℕ)^135*10000000000000^103 ≤ 6209159992629^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6951711341 10000000000 6209159992629 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3197218181/10000000000 : ℝ)^135 ≤ (22434433955949/100000000000000 : ℝ)^103 := by
    have hnat : (3197218181 : ℕ)^135*100000000000000^103 ≤ 22434433955949^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3197218181 10000000000 22434433955949 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2408219491/10000000000 : ℝ)^135 ≤ (7736983053501/50000000000000 : ℝ)^103 := by
    have hnat : (2408219491 : ℕ)^135*50000000000000^103 ≤ 7736983053501^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2408219491 10000000000 7736983053501 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6951711341/10000000000 : ℝ), (3197218181/10000000000 : ℝ), (2408219491/10000000000 : ℝ)] ![(6209159992629/10000000000000 : ℝ), (22434433955949/100000000000000 : ℝ), (7736983053501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6951711341/10000000000 : ℝ)|^135 ≤ (6209159992629/10000000000000 : ℝ)^103
        have hw : |(6951711341/10000000000 : ℝ)|=(6951711341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3197218181/10000000000 : ℝ)|^135 ≤ (22434433955949/100000000000000 : ℝ)^103
        have hw : |(3197218181/10000000000 : ℝ)|=(3197218181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2408219491/10000000000 : ℝ)|^135 ≤ (7736983053501/50000000000000 : ℝ)^103
        have hw : |(2408219491/10000000000 : ℝ)|=(2408219491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306080_s1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((87939/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(87939/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((16009/25000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(16009/25000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47363/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(47363/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14179/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14179/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1407/4000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(1407/4000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79511/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79511/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s1_pow0 : (87939/100000 : ℝ) ^ (67/16 : ℝ) ≤ (58379467109012568029/100000000000000000000 : ℝ) := by
    have hpowers : (87939/100000 : ℝ)^67 ≤ (58379467109012568029/100000000000000000000 : ℝ)^16 := by
      have hnat : (87939 : ℕ)^67*100000000000000000000^16 ≤ 58379467109012568029^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87939 100000 58379467109012568029 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (87939/100000 : ℝ)) (X := (58379467109012568029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (158379467109012568029/100000000000000000000 : ℝ) ≤ (11160644741015529/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (158379467109012568029/100000000000000000000 : ℝ)^16 ≤ (11160644741015529/10000000000000000 : ℝ)^67 := by
      have hnat : (158379467109012568029 : ℕ)^16*10000000000000000^67 ≤ 11160644741015529^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        158379467109012568029 100000000000000000000 11160644741015529 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11160644741015529/10000000000000000 : ℝ)) (X := (158379467109012568029/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (108379467109012568029/50000000000000000000 : ℝ) ≤ (12029104980944061/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (108379467109012568029/50000000000000000000 : ℝ)^16 ≤ (12029104980944061/10000000000000000 : ℝ)^67 := by
      have hnat : (108379467109012568029 : ℕ)^16*10000000000000000^67 ≤ 12029104980944061^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108379467109012568029 50000000000000000000 12029104980944061 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12029104980944061/10000000000000000 : ℝ)) (X := (108379467109012568029/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1160644741015529/8793900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(72371686660711/732825000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (87939/100000 : ℝ)) (alpha := (1160644741015529/8793900000000000 : ℝ)) (beta := (72371686660711/732825000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (87939/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1160644741015529/8793900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(72371686660711/732825000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (16009/25000 : ℝ) ^ (67/16 : ℝ) ≤ (15466830300074367327/100000000000000000000 : ℝ) := by
    have hpowers : (16009/25000 : ℝ)^67 ≤ (15466830300074367327/100000000000000000000 : ℝ)^16 := by
      have hnat : (16009 : ℕ)^67*100000000000000000000^16 ≤ 15466830300074367327^16*25000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16009 25000 15466830300074367327 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16009/25000 : ℝ)) (X := (15466830300074367327/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (115466830300074367327/100000000000000000000 : ℝ) ≤ (1293674970793219/1250000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (115466830300074367327/100000000000000000000 : ℝ)^16 ≤ (1293674970793219/1250000000000000 : ℝ)^67 := by
      have hnat : (115466830300074367327 : ℕ)^16*1250000000000000^67 ≤ 1293674970793219^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        115466830300074367327 100000000000000000000 1293674970793219 1250000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1293674970793219/1250000000000000 : ℝ)) (X := (115466830300074367327/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (65466830300074367327/50000000000000000000 : ℝ) ≤ (2666198994438771/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (65466830300074367327/50000000000000000000 : ℝ)^16 ≤ (2666198994438771/2500000000000000 : ℝ)^67 := by
      have hnat : (65466830300074367327 : ℕ)^16*2500000000000000^67 ≤ 2666198994438771^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65466830300074367327 50000000000000000000 2666198994438771 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2666198994438771/2500000000000000 : ℝ)) (X := (65466830300074367327/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(43674970793219/800450000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(78849052852333/1600900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (16009/25000 : ℝ)) (alpha := (43674970793219/800450000000000 : ℝ)) (beta := (78849052852333/1600900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (16009/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(43674970793219/800450000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(78849052852333/1600900000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (47363/50000 : ℝ) ^ (67/16 : ℝ) ≤ (15940236672285547601/20000000000000000000 : ℝ) := by
    have hpowers : (47363/50000 : ℝ)^67 ≤ (15940236672285547601/20000000000000000000 : ℝ)^16 := by
      have hnat : (47363 : ℕ)^67*20000000000000000000^16 ≤ 15940236672285547601^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47363 50000 15940236672285547601 20000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47363/50000 : ℝ)) (X := (15940236672285547601/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (35940236672285547601/20000000000000000000 : ℝ) ≤ (5751197579241831/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (35940236672285547601/20000000000000000000 : ℝ)^16 ≤ (5751197579241831/5000000000000000 : ℝ)^67 := by
      have hnat : (35940236672285547601 : ℕ)^16*5000000000000000^67 ≤ 5751197579241831^67*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35940236672285547601 20000000000000000000 5751197579241831 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5751197579241831/5000000000000000 : ℝ)) (X := (35940236672285547601/20000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25940236672285547601/10000000000000000000 : ℝ) ≤ (6278117668997653/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (25940236672285547601/10000000000000000000 : ℝ)^16 ≤ (6278117668997653/5000000000000000 : ℝ)^67 := by
      have hnat : (25940236672285547601 : ℕ)^16*5000000000000000^67 ≤ 6278117668997653^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25940236672285547601 10000000000000000000 6278117668997653 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6278117668997653/5000000000000000 : ℝ)) (X := (25940236672285547601/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(751197579241831/4736300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(263460044877911/2368150000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (47363/50000 : ℝ)) (alpha := (751197579241831/4736300000000000 : ℝ)) (beta := (263460044877911/2368150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (47363/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(751197579241831/4736300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(263460044877911/2368150000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3251942149/10000000000 : ℝ)*X 0 0+(582407949/1000000000 : ℝ)*X 0 1+(188402481/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306080_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((716544929/2500000000 : ℝ)*X 2 0+(6510635511/10000000000 : ℝ)*X 2 1+(-830265953/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306080_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4440367771/10000000000 : ℝ)*X 0 0+(4596821487/10000000000 : ℝ)*X 0 1+(3928594347/10000000000 : ℝ)*X 0 2+(4440367771/10000000000 : ℝ)*X 1 0+(4596821487/10000000000 : ℝ)*X 1 1+(3928594347/10000000000 : ℝ)*X 1 2+(4440367771/10000000000 : ℝ)*X 2 0+(4596821487/10000000000 : ℝ)*X 2 1+(3928594347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306080_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-448969521/1250000000 : ℝ)*X 0 0+(3885682203/10000000000 : ℝ)*X 0 1+(33928507/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306080_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((19589697/40000000 : ℝ)*X 1 0+(62479937/5000000000 : ℝ)*X 1 1+(851349637/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306080_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((273262181/2500000000 : ℝ)*X 2 0+(4078175957/5000000000 : ℝ)*X 2 1+(-2696466179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306080_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((573184801/2000000000 : ℝ)*X 0 0+(815657253/1250000000 : ℝ)*X 0 1+(3303263087/10000000000 : ℝ)*X 0 2+(573184801/2000000000 : ℝ)*X 1 0+(815657253/1250000000 : ℝ)*X 1 1+(3303263087/10000000000 : ℝ)*X 1 2+(573184801/2000000000 : ℝ)*X 2 0+(815657253/1250000000 : ℝ)*X 2 1+(3303263087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306080_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-5501846109/10000000000 : ℝ)*X 0 0+(1360628683/2500000000 : ℝ)*X 0 1+(1626366097/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306080_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((351002961/625000000 : ℝ)*X 1 0+(1657173/125000000 : ℝ)*X 1 1+(6134959087/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306080_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1236804241/10000000000 : ℝ)*X 2 0+(5608552759/10000000000 : ℝ)*X 2 1+(-5591594933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306080_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((351002961/625000000 : ℝ)*X 0 0+(135497707/312500000 : ℝ)*X 0 1+(288534023/1000000000 : ℝ)*X 0 2+(351002961/625000000 : ℝ)*X 1 0+(135497707/312500000 : ℝ)*X 1 1+(288534023/1000000000 : ℝ)*X 1 2+(351002961/625000000 : ℝ)*X 2 0+(135497707/312500000 : ℝ)*X 2 1+(288534023/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306080_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-2474121041/10000000000 : ℝ)*X 0 0+(3520956551/5000000000 : ℝ)*X 0 1+(3020020811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306080_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7972035111/10000000000 : ℝ)*X 1 0+(3454357/5000000000 : ℝ)*X 1 1+(443218711/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306080_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((537244133/5000000000 : ℝ)*X 2 0+(506337621/625000000 : ℝ)*X 2 1+(-696849267/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306080_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((6951711341/10000000000 : ℝ)*X 0 0+(3197218181/10000000000 : ℝ)*X 0 1+(2408219491/10000000000 : ℝ)*X 0 2+(6951711341/10000000000 : ℝ)*X 1 0+(3197218181/10000000000 : ℝ)*X 1 1+(2408219491/10000000000 : ℝ)*X 1 2+(6951711341/10000000000 : ℝ)*X 2 0+(3197218181/10000000000 : ℝ)*X 2 1+(2408219491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306080_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((14179/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14179/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16768476069249278316042272659871/1111306053428550000000000000000000000 : ℝ) := by norm_num
    linear_combination (43324857331/50000000000 : ℝ)*(base7) + (470261733993/1000000000000 : ℝ)*(base49) + (3567037/500000000000 : ℝ)*(base50) + (7175317/1000000000000 : ℝ)*(base53) + (2337802303/500000000000 : ℝ)*(base60) + (1108973119603/500000000000 : ℝ)*(major_s1_0) + (1108973119603/500000000000 : ℝ)*(major_s1_1) + (2217939063889/1000000000000 : ℝ)*(major_s1_2) + (46784641/1000000000000 : ℝ)*(sp_s1_0) + (2460135151093/1000000000000 : ℝ)*(sp_s1_7) + (1230090967867/500000000000 : ℝ)*(sp_s1_8) + (2459927879263/1000000000000 : ℝ)*(sp_s1_9) + (576246145839/250000000000 : ℝ)*(sp_s1_13) + (65307947/250000000000 : ℝ)*(sp_s1_23) + (22476366199/15625000000 : ℝ)*(f.failure) + (2460189111051/1000000000000 : ℝ)*(f.sum) + (22563808631078890733/75823426700000000000000000000000 : ℝ)*base62 + (37017550919701/148009375000000000000000000 : ℝ)*base64 + (36093086710523/400225000000000000000000000 : ℝ)*base67 + (1086174911424359/4736300000000000000000000000 : ℝ)*base69 + (28755434505842797219/104126371425000000000000000000000 : ℝ)*base70 + (8999243021963/91603125000000000000000000 : ℝ)*base72 + (403024962769799/800450000000000000000000000 : ℝ)*base74 + (246134881449343/4396950000000000000000000000 : ℝ)*base76 + (4684144516076601271/23463590850000000000000000000000 : ℝ)*base79 + (361/1562500000000000 : ℝ)*base86 + (361/1562500000000000 : ℝ)*base88 + (361/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((1407/4000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(1407/4000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2236930745233108295298878221/1058386717551000000000000000000000 : ℝ) := by norm_num
    linear_combination (126567953911/250000000000 : ℝ)*(base3) + (139560377341/500000000000 : ℝ)*(base7) + (3957631/1000000000000 : ℝ)*(base8) + (848823/200000000000 : ℝ)*(base24) + (427380497483/500000000000 : ℝ)*(base49) + (24071/500000000000 : ℝ)*(base60) + (336600297663/200000000000 : ℝ)*(major_s1_0) + (336600297663/200000000000 : ℝ)*(major_s1_1) + (336600297663/200000000000 : ℝ)*(major_s1_2) + (2051797/1000000000000 : ℝ)*(sp_s1_6) + (2101409272913/1000000000000 : ℝ)*(sp_s1_14) + (651921261547/250000000000 : ℝ)*(sp_s1_15) + (2101408986429/1000000000000 : ℝ)*(sp_s1_16) + (216096660831/250000000000 : ℝ)*(sp_s1_20) + (272884939021/250000000000 : ℝ)*(f.failure) + (131338326909/62500000000 : ℝ)*(f.sum) + (202323737448432507/541595905000000000000000000000 : ℝ)*base62 + (14626029293697/23681500000000000000000000 : ℝ)*base65 + (5317925356149/22870000000000000000000000 : ℝ)*base67 + (246598793105679/947260000000000000000000000 : ℝ)*base69 + (2319117176610776731/5553406476000000000000000000000 : ℝ)*base71 + (40107011715877/97710000000000000000000000 : ℝ)*base73 + (5358562565197/45740000000000000000000000 : ℝ)*base74 + (263103205613233/586260000000000000000000000 : ℝ)*base77 + (26694960768767659/223462770000000000000000000000 : ℝ)*base79 + (8453/12500000000000000 : ℝ)*base87 + (8453/12500000000000000 : ℝ)*base89 + (8453/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79511/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79511/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (75121159944274628983337995249/8819889312925000000000000000000000 : ℝ) := by norm_num
    linear_combination (90494664007/100000000000 : ℝ)*(base7) + (516769/100000000000 : ℝ)*(base11) + (52901013357/250000000000 : ℝ)*(base40) + (108130841901/500000000000 : ℝ)*(base49) + (2213522514183/1000000000000 : ℝ)*(major_s1_0) + (2213522514183/1000000000000 : ℝ)*(major_s1_1) + (2213522514183/1000000000000 : ℝ)*(major_s1_2) + (18397661/1000000000000 : ℝ)*(sp_s1_2) + (91423953/200000000000 : ℝ)*(sp_s1_9) + (31247/31250000000 : ℝ)*(sp_s1_14) + (2430368850499/1000000000000 : ℝ)*(sp_s1_21) + (2430375018093/1000000000000 : ℝ)*(sp_s1_22) + (2429899500667/1000000000000 : ℝ)*(sp_s1_23) + (2340564993347/1000000000000 : ℝ)*(sp_s1_27) + (1435618353277/1000000000000 : ℝ)*(f.failure) + (2430375018093/1000000000000 : ℝ)*(f.sum) + (244273271709242683/947792833750000000000000000000 : ℝ)*base62 + (581130844552091/1184075000000000000000000000 : ℝ)*base64 + (235223042254007/800450000000000000000000000 : ℝ)*base66 + (2020544524400427/4736300000000000000000000000 : ℝ)*base68 + (490980164332782811/5553406476000000000000000000000 : ℝ)*base71 + (309531056898913/488550000000000000000000000 : ℝ)*base72 + (635090712368589/1600900000000000000000000000 : ℝ)*base74 + (218973741953731/2931300000000000000000000000 : ℝ)*base76 + (2575995024369992719/7821196950000000000000000000000 : ℝ)*base78 + (33761/50000000000000000 : ℝ)*base87 + (33761/50000000000000000 : ℝ)*base89 + (33761/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((87939/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(87939/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((16009/25000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(16009/25000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(47363/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(47363/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14179/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14179/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1407/4000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(1407/4000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79511/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79511/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306080_s1 p hpa hpb X hX hprev0

#print axioms solution

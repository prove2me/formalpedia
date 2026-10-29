-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309053_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:02:30.615223+00:00
-- url     : https://prove2.me/submissions/f085c928-b14b-4a30-836d-0db9947acdbc

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
theorem collision_support_c309053_s4_s4_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1328962977/5000000000 : ℝ)*x 0 + (2512235643/5000000000 : ℝ)*x 1 + (1006787061/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328962977/5000000000 : ℝ)^35 ≤ (2243608501761/12500000000000 : ℝ)^27 := by
    have hnat : (1328962977 : ℕ)^35*12500000000000^27 ≤ 2243608501761^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328962977 5000000000 2243608501761 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2512235643/5000000000 : ℝ)^35 ≤ (40975527383721/100000000000000 : ℝ)^27 := by
    have hnat : (2512235643 : ℕ)^35*100000000000000^27 ≤ 40975527383721^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512235643 5000000000 40975527383721 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006787061/2000000000 : ℝ)^35 ≤ (41075604593017/100000000000000 : ℝ)^27 := by
    have hnat : (1006787061 : ℕ)^35*100000000000000^27 ≤ 41075604593017^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006787061 2000000000 41075604593017 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1328962977/5000000000 : ℝ), (2512235643/5000000000 : ℝ), (1006787061/2000000000 : ℝ)] ![(2243608501761/12500000000000 : ℝ), (40975527383721/100000000000000 : ℝ), (41075604593017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1328962977/5000000000 : ℝ)|^35 ≤ (2243608501761/12500000000000 : ℝ)^27
        have hw : |(-1328962977/5000000000 : ℝ)|=(1328962977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2512235643/5000000000 : ℝ)|^35 ≤ (40975527383721/100000000000000 : ℝ)^27
        have hw : |(2512235643/5000000000 : ℝ)|=(2512235643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1006787061/2000000000 : ℝ)|^35 ≤ (41075604593017/100000000000000 : ℝ)^27
        have hw : |(1006787061/2000000000 : ℝ)|=(1006787061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s4_s4_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (179873463/400000000 : ℝ)*x 0 + (-2177296943/10000000000 : ℝ)*x 1 + (5917390857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179873463/400000000 : ℝ)^35 ≤ (8871657640579/25000000000000 : ℝ)^27 := by
    have hnat : (179873463 : ℕ)^35*25000000000000^27 ≤ 8871657640579^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179873463 400000000 8871657640579 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177296943/10000000000 : ℝ)^35 ≤ (3464855498629/25000000000000 : ℝ)^27 := by
    have hnat : (2177296943 : ℕ)^35*25000000000000^27 ≤ 3464855498629^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177296943 10000000000 3464855498629 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5917390857/10000000000 : ℝ)^35 ≤ (50653947425861/100000000000000 : ℝ)^27 := by
    have hnat : (5917390857 : ℕ)^35*100000000000000^27 ≤ 50653947425861^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5917390857 10000000000 50653947425861 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(179873463/400000000 : ℝ), (-2177296943/10000000000 : ℝ), (5917390857/10000000000 : ℝ)] ![(8871657640579/25000000000000 : ℝ), (3464855498629/25000000000000 : ℝ), (50653947425861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(179873463/400000000 : ℝ)|^35 ≤ (8871657640579/25000000000000 : ℝ)^27
        have hw : |(179873463/400000000 : ℝ)|=(179873463/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2177296943/10000000000 : ℝ)|^35 ≤ (3464855498629/25000000000000 : ℝ)^27
        have hw : |(-2177296943/10000000000 : ℝ)|=(2177296943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5917390857/10000000000 : ℝ)|^35 ≤ (50653947425861/100000000000000 : ℝ)^27
        have hw : |(5917390857/10000000000 : ℝ)|=(5917390857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s4_s4_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4509962637/10000000000 : ℝ)*x 0 + (1477887471/2500000000 : ℝ)*x 1 + (-1084432967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4509962637/10000000000 : ℝ)^35 ≤ (4452620496121/12500000000000 : ℝ)^27 := by
    have hnat : (4509962637 : ℕ)^35*12500000000000^27 ≤ 4452620496121^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509962637 10000000000 4452620496121 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1477887471/2500000000 : ℝ)^35 ≤ (2529457117753/5000000000000 : ℝ)^27 := by
    have hnat : (1477887471 : ℕ)^35*5000000000000^27 ≤ 2529457117753^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1477887471 2500000000 2529457117753 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084432967/5000000000 : ℝ)^35 ≤ (2757978731211/20000000000000 : ℝ)^27 := by
    have hnat : (1084432967 : ℕ)^35*20000000000000^27 ≤ 2757978731211^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084432967 5000000000 2757978731211 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4509962637/10000000000 : ℝ), (1477887471/2500000000 : ℝ), (-1084432967/5000000000 : ℝ)] ![(4452620496121/12500000000000 : ℝ), (2529457117753/5000000000000 : ℝ), (2757978731211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4509962637/10000000000 : ℝ)|^35 ≤ (4452620496121/12500000000000 : ℝ)^27
        have hw : |(4509962637/10000000000 : ℝ)|=(4509962637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1477887471/2500000000 : ℝ)|^35 ≤ (2529457117753/5000000000000 : ℝ)^27
        have hw : |(1477887471/2500000000 : ℝ)|=(1477887471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1084432967/5000000000 : ℝ)|^35 ≤ (2757978731211/20000000000000 : ℝ)^27
        have hw : |(-1084432967/5000000000 : ℝ)|=(1084432967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s4_s4_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3163750003/5000000000 : ℝ)*x 0 + (3158044641/10000000000 : ℝ)*x 1 + (314300409/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3163750003/5000000000 : ℝ)^35 ≤ (55250724556593/100000000000000 : ℝ)^27 := by
    have hnat : (3163750003 : ℕ)^35*100000000000000^27 ≤ 55250724556593^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3163750003 5000000000 55250724556593 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3158044641/10000000000 : ℝ)^35 ≤ (22443870314917/100000000000000 : ℝ)^27 := by
    have hnat : (3158044641 : ℕ)^35*100000000000000^27 ≤ 22443870314917^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3158044641 10000000000 22443870314917 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314300409/1000000000 : ℝ)^35 ≤ (22305405115671/100000000000000 : ℝ)^27 := by
    have hnat : (314300409 : ℕ)^35*100000000000000^27 ≤ 22305405115671^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314300409 1000000000 22305405115671 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3163750003/5000000000 : ℝ), (3158044641/10000000000 : ℝ), (314300409/1000000000 : ℝ)] ![(55250724556593/100000000000000 : ℝ), (22443870314917/100000000000000 : ℝ), (22305405115671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3163750003/5000000000 : ℝ)|^35 ≤ (55250724556593/100000000000000 : ℝ)^27
        have hw : |(3163750003/5000000000 : ℝ)|=(3163750003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3158044641/10000000000 : ℝ)|^35 ≤ (22443870314917/100000000000000 : ℝ)^27
        have hw : |(3158044641/10000000000 : ℝ)|=(3158044641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(314300409/1000000000 : ℝ)|^35 ≤ (22305405115671/100000000000000 : ℝ)^27
        have hw : |(314300409/1000000000 : ℝ)|=(314300409/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s4_s4_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-105344963/400000000 : ℝ)*x 0 + (4561083209/10000000000 : ℝ)*x 1 + (5504305527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105344963/400000000 : ℝ)^35 ≤ (17736422100307/100000000000000 : ℝ)^27 := by
    have hnat : (105344963 : ℕ)^35*100000000000000^27 ≤ 17736422100307^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105344963 400000000 17736422100307 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4561083209/10000000000 : ℝ)^35 ≤ (36145239351549/100000000000000 : ℝ)^27 := by
    have hnat : (4561083209 : ℕ)^35*100000000000000^27 ≤ 36145239351549^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4561083209 10000000000 36145239351549 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5504305527/10000000000 : ℝ)^35 ≤ (23059169264777/50000000000000 : ℝ)^27 := by
    have hnat : (5504305527 : ℕ)^35*50000000000000^27 ≤ 23059169264777^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504305527 10000000000 23059169264777 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105344963/400000000 : ℝ), (4561083209/10000000000 : ℝ), (5504305527/10000000000 : ℝ)] ![(17736422100307/100000000000000 : ℝ), (36145239351549/100000000000000 : ℝ), (23059169264777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105344963/400000000 : ℝ)|^35 ≤ (17736422100307/100000000000000 : ℝ)^27
        have hw : |(-105344963/400000000 : ℝ)|=(105344963/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4561083209/10000000000 : ℝ)|^35 ≤ (36145239351549/100000000000000 : ℝ)^27
        have hw : |(4561083209/10000000000 : ℝ)|=(4561083209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5504305527/10000000000 : ℝ)|^35 ≤ (23059169264777/50000000000000 : ℝ)^27
        have hw : |(5504305527/10000000000 : ℝ)|=(5504305527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s4_s4_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (87763019/200000000 : ℝ)*x 0 + (-49226513/250000000 : ℝ)*x 1 + (6168265927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87763019/200000000 : ℝ)^35 ≤ (17189407753703/50000000000000 : ℝ)^27 := by
    have hnat : (87763019 : ℕ)^35*50000000000000^27 ≤ 17189407753703^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87763019 200000000 17189407753703 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49226513/250000000 : ℝ)^35 ≤ (760379949877/6250000000000 : ℝ)^27 := by
    have hnat : (49226513 : ℕ)^35*6250000000000^27 ≤ 760379949877^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49226513 250000000 760379949877 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6168265927/10000000000 : ℝ)^35 ≤ (10691021054981/20000000000000 : ℝ)^27 := by
    have hnat : (6168265927 : ℕ)^35*20000000000000^27 ≤ 10691021054981^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6168265927 10000000000 10691021054981 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87763019/200000000 : ℝ), (-49226513/250000000 : ℝ), (6168265927/10000000000 : ℝ)] ![(17189407753703/50000000000000 : ℝ), (760379949877/6250000000000 : ℝ), (10691021054981/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87763019/200000000 : ℝ)|^35 ≤ (17189407753703/50000000000000 : ℝ)^27
        have hw : |(87763019/200000000 : ℝ)|=(87763019/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49226513/250000000 : ℝ)|^35 ≤ (760379949877/6250000000000 : ℝ)^27
        have hw : |(-49226513/250000000 : ℝ)|=(49226513/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6168265927/10000000000 : ℝ)|^35 ≤ (10691021054981/20000000000000 : ℝ)^27
        have hw : |(6168265927/10000000000 : ℝ)|=(6168265927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s4_s4_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (440129521/1000000000 : ℝ)*x 0 + (3168871263/5000000000 : ℝ)*x 1 + (-427109451/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440129521/1000000000 : ℝ)^35 ≤ (17256182511599/50000000000000 : ℝ)^27 := by
    have hnat : (440129521 : ℕ)^35*50000000000000^27 ≤ 17256182511599^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440129521 1000000000 17256182511599 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3168871263/5000000000 : ℝ)^35 ≤ (55366687978259/100000000000000 : ℝ)^27 := by
    have hnat : (3168871263 : ℕ)^35*100000000000000^27 ≤ 55366687978259^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3168871263 5000000000 55366687978259 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427109451/2500000000 : ℝ)^35 ≤ (506047349279/5000000000000 : ℝ)^27 := by
    have hnat : (427109451 : ℕ)^35*5000000000000^27 ≤ 506047349279^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427109451 2500000000 506047349279 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(440129521/1000000000 : ℝ), (3168871263/5000000000 : ℝ), (-427109451/2500000000 : ℝ)] ![(17256182511599/50000000000000 : ℝ), (55366687978259/100000000000000 : ℝ), (506047349279/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(440129521/1000000000 : ℝ)|^35 ≤ (17256182511599/50000000000000 : ℝ)^27
        have hw : |(440129521/1000000000 : ℝ)|=(440129521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3168871263/5000000000 : ℝ)|^35 ≤ (55366687978259/100000000000000 : ℝ)^27
        have hw : |(3168871263/5000000000 : ℝ)|=(3168871263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427109451/2500000000 : ℝ)|^35 ≤ (506047349279/5000000000000 : ℝ)^27
        have hw : |(-427109451/2500000000 : ℝ)|=(427109451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s4_s4_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6266387163/10000000000 : ℝ)*x 0 + (3733839381/10000000000 : ℝ)*x 1 + (2612700933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6266387163/10000000000 : ℝ)^35 ≤ (27279988532079/50000000000000 : ℝ)^27 := by
    have hnat : (6266387163 : ℕ)^35*50000000000000^27 ≤ 27279988532079^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6266387163 10000000000 27279988532079 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3733839381/10000000000 : ℝ)^35 ≤ (139430227057/500000000000 : ℝ)^27 := by
    have hnat : (3733839381 : ℕ)^35*500000000000^27 ≤ 139430227057^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3733839381 10000000000 139430227057 500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2612700933/10000000000 : ℝ)^35 ≤ (70215910023/400000000000 : ℝ)^27 := by
    have hnat : (2612700933 : ℕ)^35*400000000000^27 ≤ 70215910023^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612700933 10000000000 70215910023 400000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6266387163/10000000000 : ℝ), (3733839381/10000000000 : ℝ), (2612700933/10000000000 : ℝ)] ![(27279988532079/50000000000000 : ℝ), (139430227057/500000000000 : ℝ), (70215910023/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6266387163/10000000000 : ℝ)|^35 ≤ (27279988532079/50000000000000 : ℝ)^27
        have hw : |(6266387163/10000000000 : ℝ)|=(6266387163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3733839381/10000000000 : ℝ)|^35 ≤ (139430227057/500000000000 : ℝ)^27
        have hw : |(3733839381/10000000000 : ℝ)|=(3733839381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2612700933/10000000000 : ℝ)|^35 ≤ (70215910023/400000000000 : ℝ)^27
        have hw : |(2612700933/10000000000 : ℝ)|=(2612700933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s4_s4_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2203937911/10000000000 : ℝ)*x 0 + (4960380181/10000000000 : ℝ)*x 1 + (218338637/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2203937911/10000000000 : ℝ)^35 ≤ (14079646696361/100000000000000 : ℝ)^27 := by
    have hnat : (2203937911 : ℕ)^35*100000000000000^27 ≤ 14079646696361^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203937911 10000000000 14079646696361 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4960380181/10000000000 : ℝ)^35 ≤ (20149634808423/50000000000000 : ℝ)^27 := by
    have hnat : (4960380181 : ℕ)^35*50000000000000^27 ≤ 20149634808423^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4960380181 10000000000 20149634808423 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218338637/400000000 : ℝ)^35 ≤ (11405270917339/25000000000000 : ℝ)^27 := by
    have hnat : (218338637 : ℕ)^35*25000000000000^27 ≤ 11405270917339^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218338637 400000000 11405270917339 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2203937911/10000000000 : ℝ), (4960380181/10000000000 : ℝ), (218338637/400000000 : ℝ)] ![(14079646696361/100000000000000 : ℝ), (20149634808423/50000000000000 : ℝ), (11405270917339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2203937911/10000000000 : ℝ)|^35 ≤ (14079646696361/100000000000000 : ℝ)^27
        have hw : |(-2203937911/10000000000 : ℝ)|=(2203937911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4960380181/10000000000 : ℝ)|^35 ≤ (20149634808423/50000000000000 : ℝ)^27
        have hw : |(4960380181/10000000000 : ℝ)|=(4960380181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218338637/400000000 : ℝ)|^35 ≤ (11405270917339/25000000000000 : ℝ)^27
        have hw : |(218338637/400000000 : ℝ)|=(218338637/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s4_s4_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1066960953/2500000000 : ℝ)*x 0 + (-519633721/2500000000 : ℝ)*x 1 + (1549469011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066960953/2500000000 : ℝ)^35 ≤ (33161996620261/100000000000000 : ℝ)^27 := by
    have hnat : (1066960953 : ℕ)^35*100000000000000^27 ≤ 33161996620261^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066960953 2500000000 33161996620261 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519633721/2500000000 : ℝ)^35 ≤ (13050024821159/100000000000000 : ℝ)^27 := by
    have hnat : (519633721 : ℕ)^35*100000000000000^27 ≤ 13050024821159^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519633721 2500000000 13050024821159 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1549469011/2500000000 : ℝ)^35 ≤ (53787978531233/100000000000000 : ℝ)^27 := by
    have hnat : (1549469011 : ℕ)^35*100000000000000^27 ≤ 53787978531233^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1549469011 2500000000 53787978531233 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066960953/2500000000 : ℝ), (-519633721/2500000000 : ℝ), (1549469011/2500000000 : ℝ)] ![(33161996620261/100000000000000 : ℝ), (13050024821159/100000000000000 : ℝ), (53787978531233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066960953/2500000000 : ℝ)|^35 ≤ (33161996620261/100000000000000 : ℝ)^27
        have hw : |(1066960953/2500000000 : ℝ)|=(1066960953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-519633721/2500000000 : ℝ)|^35 ≤ (13050024821159/100000000000000 : ℝ)^27
        have hw : |(-519633721/2500000000 : ℝ)|=(519633721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1549469011/2500000000 : ℝ)|^35 ≤ (53787978531233/100000000000000 : ℝ)^27
        have hw : |(1549469011/2500000000 : ℝ)|=(1549469011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s4_s4_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4973843873/10000000000 : ℝ)*x 0 + (577545133/1000000000 : ℝ)*x 1 + (-438568859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4973843873/10000000000 : ℝ)^35 ≤ (40441118247583/100000000000000 : ℝ)^27 := by
    have hnat : (4973843873 : ℕ)^35*100000000000000^27 ≤ 40441118247583^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4973843873 10000000000 40441118247583 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (577545133/1000000000 : ℝ)^35 ≤ (9816907924503/20000000000000 : ℝ)^27 := by
    have hnat : (577545133 : ℕ)^35*20000000000000^27 ≤ 9816907924503^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      577545133 1000000000 9816907924503 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438568859/2500000000 : ℝ)^35 ≤ (81830797771/781250000000 : ℝ)^27 := by
    have hnat : (438568859 : ℕ)^35*781250000000^27 ≤ 81830797771^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438568859 2500000000 81830797771 781250000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4973843873/10000000000 : ℝ), (577545133/1000000000 : ℝ), (-438568859/2500000000 : ℝ)] ![(40441118247583/100000000000000 : ℝ), (9816907924503/20000000000000 : ℝ), (81830797771/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4973843873/10000000000 : ℝ)|^35 ≤ (40441118247583/100000000000000 : ℝ)^27
        have hw : |(4973843873/10000000000 : ℝ)|=(4973843873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(577545133/1000000000 : ℝ)|^35 ≤ (9816907924503/20000000000000 : ℝ)^27
        have hw : |(577545133/1000000000 : ℝ)|=(577545133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-438568859/2500000000 : ℝ)|^35 ≤ (81830797771/781250000000 : ℝ)^27
        have hw : |(-438568859/2500000000 : ℝ)|=(438568859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s4_s4_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6841395007/10000000000 : ℝ)*x 0 + (3095697643/10000000000 : ℝ)*x 1 + (2548005253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6841395007/10000000000 : ℝ)^35 ≤ (61136228221049/100000000000000 : ℝ)^27 := by
    have hnat : (6841395007 : ℕ)^35*100000000000000^27 ≤ 61136228221049^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6841395007 10000000000 61136228221049 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3095697643/10000000000 : ℝ)^35 ≤ (273389726149/1250000000000 : ℝ)^27 := by
    have hnat : (3095697643 : ℕ)^35*1250000000000^27 ≤ 273389726149^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3095697643 10000000000 273389726149 1250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2548005253/10000000000 : ℝ)^35 ≤ (8496296838637/50000000000000 : ℝ)^27 := by
    have hnat : (2548005253 : ℕ)^35*50000000000000^27 ≤ 8496296838637^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548005253 10000000000 8496296838637 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6841395007/10000000000 : ℝ), (3095697643/10000000000 : ℝ), (2548005253/10000000000 : ℝ)] ![(61136228221049/100000000000000 : ℝ), (273389726149/1250000000000 : ℝ), (8496296838637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6841395007/10000000000 : ℝ)|^35 ≤ (61136228221049/100000000000000 : ℝ)^27
        have hw : |(6841395007/10000000000 : ℝ)|=(6841395007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3095697643/10000000000 : ℝ)|^35 ≤ (273389726149/1250000000000 : ℝ)^27
        have hw : |(3095697643/10000000000 : ℝ)|=(3095697643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2548005253/10000000000 : ℝ)|^35 ≤ (8496296838637/50000000000000 : ℝ)^27
        have hw : |(2548005253/10000000000 : ℝ)|=(2548005253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s4_s4_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-13496033/62500000 : ℝ)*x 0 + (2611983529/5000000000 : ℝ)*x 1 + (523282611/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13496033/62500000 : ℝ)^35 ≤ (13711640156103/100000000000000 : ℝ)^27 := by
    have hnat : (13496033 : ℕ)^35*100000000000000^27 ≤ 13711640156103^27*62500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13496033 62500000 13711640156103 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2611983529/5000000000 : ℝ)^35 ≤ (21548398860139/50000000000000 : ℝ)^27 := by
    have hnat : (2611983529 : ℕ)^35*50000000000000^27 ≤ 21548398860139^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611983529 5000000000 21548398860139 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523282611/1000000000 : ℝ)^35 ≤ (43191562107017/100000000000000 : ℝ)^27 := by
    have hnat : (523282611 : ℕ)^35*100000000000000^27 ≤ 43191562107017^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523282611 1000000000 43191562107017 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13496033/62500000 : ℝ), (2611983529/5000000000 : ℝ), (523282611/1000000000 : ℝ)] ![(13711640156103/100000000000000 : ℝ), (21548398860139/50000000000000 : ℝ), (43191562107017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13496033/62500000 : ℝ)|^35 ≤ (13711640156103/100000000000000 : ℝ)^27
        have hw : |(-13496033/62500000 : ℝ)|=(13496033/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2611983529/5000000000 : ℝ)|^35 ≤ (21548398860139/50000000000000 : ℝ)^27
        have hw : |(2611983529/5000000000 : ℝ)|=(2611983529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523282611/1000000000 : ℝ)|^35 ≤ (43191562107017/100000000000000 : ℝ)^27
        have hw : |(523282611/1000000000 : ℝ)|=(523282611/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s4_s4_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2502635959/5000000000 : ℝ)*x 0 + (-1800459541/10000000000 : ℝ)*x 1 + (114253661/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2502635959/5000000000 : ℝ)^35 ≤ (509658442541/1250000000000 : ℝ)^27 := by
    have hnat : (2502635959 : ℕ)^35*1250000000000^27 ≤ 509658442541^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502635959 5000000000 509658442541 1250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1800459541/10000000000 : ℝ)^35 ≤ (2708296600503/25000000000000 : ℝ)^27 := by
    have hnat : (1800459541 : ℕ)^35*25000000000000^27 ≤ 2708296600503^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800459541 10000000000 2708296600503 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114253661/200000000 : ℝ)^35 ≤ (3024633636187/6250000000000 : ℝ)^27 := by
    have hnat : (114253661 : ℕ)^35*6250000000000^27 ≤ 3024633636187^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114253661 200000000 3024633636187 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2502635959/5000000000 : ℝ), (-1800459541/10000000000 : ℝ), (114253661/200000000 : ℝ)] ![(509658442541/1250000000000 : ℝ), (2708296600503/25000000000000 : ℝ), (3024633636187/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2502635959/5000000000 : ℝ)|^35 ≤ (509658442541/1250000000000 : ℝ)^27
        have hw : |(2502635959/5000000000 : ℝ)|=(2502635959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1800459541/10000000000 : ℝ)|^35 ≤ (2708296600503/25000000000000 : ℝ)^27
        have hw : |(-1800459541/10000000000 : ℝ)|=(1800459541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(114253661/200000000 : ℝ)|^35 ≤ (3024633636187/6250000000000 : ℝ)^27
        have hw : |(114253661/200000000 : ℝ)|=(114253661/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s4_s4_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4259337487/10000000000 : ℝ)*x 0 + (3136964871/5000000000 : ℝ)*x 1 + (-1983086469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259337487/10000000000 : ℝ)^35 ≤ (16538171069519/50000000000000 : ℝ)^27 := by
    have hnat : (4259337487 : ℕ)^35*50000000000000^27 ≤ 16538171069519^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259337487 10000000000 16538171069519 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3136964871/5000000000 : ℝ)^35 ≤ (2732256097009/5000000000000 : ℝ)^27 := by
    have hnat : (3136964871 : ℕ)^35*5000000000000^27 ≤ 2732256097009^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3136964871 5000000000 2732256097009 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1983086469/10000000000 : ℝ)^35 ≤ (6139267958719/50000000000000 : ℝ)^27 := by
    have hnat : (1983086469 : ℕ)^35*50000000000000^27 ≤ 6139267958719^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983086469 10000000000 6139267958719 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259337487/10000000000 : ℝ), (3136964871/5000000000 : ℝ), (-1983086469/10000000000 : ℝ)] ![(16538171069519/50000000000000 : ℝ), (2732256097009/5000000000000 : ℝ), (6139267958719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259337487/10000000000 : ℝ)|^35 ≤ (16538171069519/50000000000000 : ℝ)^27
        have hw : |(4259337487/10000000000 : ℝ)|=(4259337487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3136964871/5000000000 : ℝ)|^35 ≤ (2732256097009/5000000000000 : ℝ)^27
        have hw : |(3136964871/5000000000 : ℝ)|=(3136964871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1983086469/10000000000 : ℝ)|^35 ≤ (6139267958719/50000000000000 : ℝ)^27
        have hw : |(-1983086469/10000000000 : ℝ)|=(1983086469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309053_s4_s4_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1722175047/2500000000 : ℝ)*x 0 + (1396645311/5000000000 : ℝ)*x 1 + (1398327881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1722175047/2500000000 : ℝ)^35 ≤ (15421192875327/25000000000000 : ℝ)^27 := by
    have hnat : (1722175047 : ℕ)^35*25000000000000^27 ≤ 15421192875327^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722175047 2500000000 15421192875327 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1396645311/5000000000 : ℝ)^35 ≤ (19142664245263/100000000000000 : ℝ)^27 := by
    have hnat : (1396645311 : ℕ)^35*100000000000000^27 ≤ 19142664245263^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396645311 5000000000 19142664245263 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1398327881/5000000000 : ℝ)^35 ≤ (1917256424323/10000000000000 : ℝ)^27 := by
    have hnat : (1398327881 : ℕ)^35*10000000000000^27 ≤ 1917256424323^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398327881 5000000000 1917256424323 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1722175047/2500000000 : ℝ), (1396645311/5000000000 : ℝ), (1398327881/5000000000 : ℝ)] ![(15421192875327/25000000000000 : ℝ), (19142664245263/100000000000000 : ℝ), (1917256424323/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1722175047/2500000000 : ℝ)|^35 ≤ (15421192875327/25000000000000 : ℝ)^27
        have hw : |(1722175047/2500000000 : ℝ)|=(1722175047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1396645311/5000000000 : ℝ)|^35 ≤ (19142664245263/100000000000000 : ℝ)^27
        have hw : |(1396645311/5000000000 : ℝ)|=(1396645311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1398327881/5000000000 : ℝ)|^35 ≤ (1917256424323/10000000000000 : ℝ)^27
        have hw : |(1398327881/5000000000 : ℝ)|=(1398327881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309053_s4 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((1231/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1231/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45597/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(45597/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22027/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22027/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10481/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10481/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1247/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1247/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4851/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4851/20000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (1231/3125 : ℝ) ^ (69/16 : ℝ) ≤ (1799687643218063157/100000000000000000000 : ℝ) := by
    have hpowers : (1231/3125 : ℝ)^69 ≤ (1799687643218063157/100000000000000000000 : ℝ)^16 := by
      have hnat : (1231 : ℕ)^69*100000000000000000000^16 ≤ 1799687643218063157^16*3125^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1231 3125 1799687643218063157 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1231/3125 : ℝ)) (X := (1799687643218063157/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s4_corner0a : (101799687643218063157/100000000000000000000 : ℝ) ≤ (627590404061387/625000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (101799687643218063157/100000000000000000000 : ℝ)^16 ≤ (627590404061387/625000000000000 : ℝ)^69 := by
      have hnat : (101799687643218063157 : ℕ)^16*625000000000000^69 ≤ 627590404061387^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101799687643218063157 100000000000000000000 627590404061387 625000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (627590404061387/625000000000000 : ℝ)) (X := (101799687643218063157/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s4_corner0b : (51799687643218063157/50000000000000000000 : ℝ) ≤ (10082333879910177/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (51799687643218063157/50000000000000000000 : ℝ)^16 ≤ (10082333879910177/10000000000000000 : ℝ)^69 := by
      have hnat : (51799687643218063157 : ℕ)^16*10000000000000000^69 ≤ 10082333879910177^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51799687643218063157 50000000000000000000 10082333879910177 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10082333879910177/10000000000000000 : ℝ)) (X := (51799687643218063157/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(2590404061387/246200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(8177482985597/787840000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1231/3125 : ℝ)) (alpha := (2590404061387/246200000000000 : ℝ)) (beta := (8177482985597/787840000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1231/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(2590404061387/246200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(8177482985597/787840000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (45597/100000 : ℝ) ^ (69/16 : ℝ) ≤ (676382961356047347/20000000000000000000 : ℝ) := by
    have hpowers : (45597/100000 : ℝ)^69 ≤ (676382961356047347/20000000000000000000 : ℝ)^16 := by
      have hnat : (45597 : ℕ)^69*20000000000000000000^16 ≤ 676382961356047347^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45597 100000 676382961356047347 20000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45597/100000 : ℝ)) (X := (676382961356047347/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s4_corner1a : (20676382961356047347/20000000000000000000 : ℝ) ≤ (10077422476874759/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (20676382961356047347/20000000000000000000 : ℝ)^16 ≤ (10077422476874759/10000000000000000 : ℝ)^69 := by
      have hnat : (20676382961356047347 : ℕ)^16*10000000000000000^69 ≤ 10077422476874759^69*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20676382961356047347 20000000000000000000 10077422476874759 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10077422476874759/10000000000000000 : ℝ)) (X := (20676382961356047347/20000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s4_corner1b : (10676382961356047347/10000000000000000000 : ℝ) ≤ (5076461654830539/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (10676382961356047347/10000000000000000000 : ℝ)^16 ≤ (5076461654830539/5000000000000000 : ℝ)^69 := by
      have hnat : (10676382961356047347 : ℕ)^16*5000000000000000^69 ≤ 5076461654830539^69*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10676382961356047347 10000000000000000000 5076461654830539 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5076461654830539/5000000000000000 : ℝ)) (X := (10676382961356047347/10000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(77422476874759/4559700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(75500832786319/4559700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (45597/100000 : ℝ)) (alpha := (77422476874759/4559700000000000 : ℝ)) (beta := (75500832786319/4559700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (45597/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(77422476874759/4559700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(75500832786319/4559700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (22027/50000 : ℝ) ^ (69/16 : ℝ) ≤ (2915323885964061857/100000000000000000000 : ℝ) := by
    have hpowers : (22027/50000 : ℝ)^69 ≤ (2915323885964061857/100000000000000000000 : ℝ)^16 := by
      have hnat : (22027 : ℕ)^69*100000000000000000000^16 ≤ 2915323885964061857^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22027 50000 2915323885964061857 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22027/50000 : ℝ)) (X := (2915323885964061857/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s4_corner2a : (102915323885964061857/100000000000000000000 : ℝ) ≤ (2516714389226083/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (102915323885964061857/100000000000000000000 : ℝ)^16 ≤ (2516714389226083/2500000000000000 : ℝ)^69 := by
      have hnat : (102915323885964061857 : ℕ)^16*2500000000000000^69 ≤ 2516714389226083^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102915323885964061857 100000000000000000000 2516714389226083 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2516714389226083/2500000000000000 : ℝ)) (X := (102915323885964061857/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s4_corner2b : (52915323885964061857/50000000000000000000 : ℝ) ≤ (1013227582711819/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (52915323885964061857/50000000000000000000 : ℝ)^16 ≤ (1013227582711819/1000000000000000 : ℝ)^69 := by
      have hnat : (52915323885964061857 : ℕ)^16*1000000000000000^69 ≤ 1013227582711819^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52915323885964061857 50000000000000000000 1013227582711819 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1013227582711819/1000000000000000 : ℝ)) (X := (52915323885964061857/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(16714389226083/1101350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(32709135106929/2202700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (22027/50000 : ℝ)) (alpha := (16714389226083/1101350000000000 : ℝ)) (beta := (32709135106929/2202700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (22027/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(16714389226083/1101350000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(32709135106929/2202700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-1328962977/5000000000 : ℝ)*X 0 0+(2512235643/5000000000 : ℝ)*X 0 1+(1006787061/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((179873463/400000000 : ℝ)*X 1 0+(-2177296943/10000000000 : ℝ)*X 1 1+(5917390857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((4509962637/10000000000 : ℝ)*X 2 0+(1477887471/2500000000 : ℝ)*X 2 1+(-1084432967/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((3163750003/5000000000 : ℝ)*X 0 0+(3158044641/10000000000 : ℝ)*X 0 1+(314300409/1000000000 : ℝ)*X 0 2+(3163750003/5000000000 : ℝ)*X 1 0+(3158044641/10000000000 : ℝ)*X 1 1+(314300409/1000000000 : ℝ)*X 1 2+(3163750003/5000000000 : ℝ)*X 2 0+(3158044641/10000000000 : ℝ)*X 2 1+(314300409/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-105344963/400000000 : ℝ)*X 0 0+(4561083209/10000000000 : ℝ)*X 0 1+(5504305527/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((87763019/200000000 : ℝ)*X 1 0+(-49226513/250000000 : ℝ)*X 1 1+(6168265927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((440129521/1000000000 : ℝ)*X 2 0+(3168871263/5000000000 : ℝ)*X 2 1+(-427109451/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((6266387163/10000000000 : ℝ)*X 0 0+(3733839381/10000000000 : ℝ)*X 0 1+(2612700933/10000000000 : ℝ)*X 0 2+(6266387163/10000000000 : ℝ)*X 1 0+(3733839381/10000000000 : ℝ)*X 1 1+(2612700933/10000000000 : ℝ)*X 1 2+(6266387163/10000000000 : ℝ)*X 2 0+(3733839381/10000000000 : ℝ)*X 2 1+(2612700933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-2203937911/10000000000 : ℝ)*X 0 0+(4960380181/10000000000 : ℝ)*X 0 1+(218338637/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((1066960953/2500000000 : ℝ)*X 1 0+(-519633721/2500000000 : ℝ)*X 1 1+(1549469011/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((4973843873/10000000000 : ℝ)*X 2 0+(577545133/1000000000 : ℝ)*X 2 1+(-438568859/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((6841395007/10000000000 : ℝ)*X 0 0+(3095697643/10000000000 : ℝ)*X 0 1+(2548005253/10000000000 : ℝ)*X 0 2+(6841395007/10000000000 : ℝ)*X 1 0+(3095697643/10000000000 : ℝ)*X 1 1+(2548005253/10000000000 : ℝ)*X 1 2+(6841395007/10000000000 : ℝ)*X 2 0+(3095697643/10000000000 : ℝ)*X 2 1+(2548005253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-13496033/62500000 : ℝ)*X 0 0+(2611983529/5000000000 : ℝ)*X 0 1+(523282611/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((2502635959/5000000000 : ℝ)*X 1 0+(-1800459541/10000000000 : ℝ)*X 1 1+(114253661/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((4259337487/10000000000 : ℝ)*X 2 0+(3136964871/5000000000 : ℝ)*X 2 1+(-1983086469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((1722175047/2500000000 : ℝ)*X 0 0+(1396645311/5000000000 : ℝ)*X 0 1+(1398327881/5000000000 : ℝ)*X 0 2+(1722175047/2500000000 : ℝ)*X 1 0+(1396645311/5000000000 : ℝ)*X 1 1+(1398327881/5000000000 : ℝ)*X 1 2+(1722175047/2500000000 : ℝ)*X 2 0+(1396645311/5000000000 : ℝ)*X 2 1+(1398327881/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309053_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((10481/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10481/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11967149887524755957606431916787/659399179460800000000000000000000000 : ℝ) := by norm_num
    linear_combination (686127674723/1000000000000 : ℝ)*(base49) + (1335444386579/1000000000000 : ℝ)*(base59) + (104253/40000000000 : ℝ)*(base60) + (10693754242803/1000000000000 : ℝ)*(major_s4_0) + (10693754242803/1000000000000 : ℝ)*(major_s4_1) + (10693754242803/1000000000000 : ℝ)*(major_s4_2) + (59910743/250000000000 : ℝ)*(sp_s4_0) + (28631999/500000000000 : ℝ)*(sp_s4_6) + (7336031491121/500000000000 : ℝ)*(sp_s4_7) + (2934390416547/200000000000 : ℝ)*(sp_s4_8) + (7335913272467/500000000000 : ℝ)*(sp_s4_9) + (6715142546863/1000000000000 : ℝ)*(sp_s4_13) + (350542479/1000000000000 : ℝ)*(sp_s4_15) + (11902007/25000000000 : ℝ)*(sp_s4_23) + (3357599905431/500000000000 : ℝ)*(f.failure) + (14672302625213/1000000000000 : ℝ)*(f.sum) + (1281016999396722189/1339153492000000000000000000000 : ℝ)*base63 + (1034865018063443/2202700000000000000000000000 : ℝ)*base65 + (751034658723211/1519900000000000000000000000 : ℝ)*base67 + (49633825620639/68834375000000000000000000 : ℝ)*base69 + (3809469262041944653/5423047400000000000000000000000 : ℝ)*base71 + (551662707111/787840000000000000000000000 : ℝ)*base73 + (491660198100729/1519900000000000000000000000 : ℝ)*base75 + (3323496897461/246200000000000000000000000 : ℝ)*base77 + (43573317313901941757/59871900800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (20457/50000000000000000 : ℝ)*base87 + (20457/50000000000000000 : ℝ)*base89 + (20457/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1247/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1247/5000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7603868028022805166141/550675000000000000000000000 : ℝ) := by norm_num
    linear_combination (266329/250000000000 : ℝ)*(base39) + (783822236549/1000000000000 : ℝ)*(base49) + (909514682441/1000000000000 : ℝ)*(base59) + (2629846827289/250000000000 : ℝ)*(major_s4_0) + (2629846827289/250000000000 : ℝ)*(major_s4_1) + (2629846827289/250000000000 : ℝ)*(major_s4_2) + (21225227/500000000000 : ℝ)*(sp_s4_1) + (48203069/1000000000000 : ℝ)*(sp_s4_2) + (63390223/500000000000 : ℝ)*(sp_s4_7) + (14432938066937/1000000000000 : ℝ)*(sp_s4_14) + (14433022396929/1000000000000 : ℝ)*(sp_s4_15) + (7216508322157/500000000000 : ℝ)*(sp_s4_16) + (3302751688103/500000000000 : ℝ)*(sp_s4_20) + (50447991/250000000000 : ℝ)*(sp_s4_27) + (660570516817/100000000000 : ℝ)*(f.failure) + (14433064847383/1000000000000 : ℝ)*(f.sum) + (2568681905057074759/10043651190000000000000000000000 : ℝ)*base63 + (26189524790643/1101350000000000000000000000 : ℝ)*base65 + (355410066600587/2279850000000000000000000000 : ℝ)*base66 + (12707164412193/275337500000000000000000000 : ℝ)*base68 + (412227126732928559/1355761850000000000000000000000 : ℝ)*base71 + (55319806952907/196960000000000000000000000 : ℝ)*base72 + (98347682569063/2279850000000000000000000000 : ℝ)*base74 + (11349534032867/61550000000000000000000000 : ℝ)*base76 + (3455100206903583973/44903925600000000000000000000000 : ℝ)*base79 + (3201/10000000000000000 : ℝ)*base86 + (3201/10000000000000000 : ℝ)*base88 + (3201/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4851/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4851/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (100847053014639466796834823063/10303112179075000000000000000000000 : ℝ) := by norm_num
    linear_combination (246725000693/1000000000000 : ℝ)*(base40) + (310118064447/500000000000 : ℝ)*(base49) + (446439239287/500000000000 : ℝ)*(base59) + (600103545051/62500000000 : ℝ)*(major_s4_0) + (600103545051/62500000000 : ℝ)*(major_s4_1) + (600103545051/62500000000 : ℝ)*(major_s4_2) + (52780117/1000000000000 : ℝ)*(sp_s4_0) + (45342477/500000000000 : ℝ)*(sp_s4_2) + (26026069/1000000000000 : ℝ)*(sp_s4_9) + (127520297/500000000000 : ℝ)*(sp_s4_20) + (3293461507769/250000000000 : ℝ)*(sp_s4_21) + (13173898811193/1000000000000 : ℝ)*(sp_s4_22) + (1317378210017/100000000000 : ℝ)*(sp_s4_23) + (1205831265433/200000000000 : ℝ)*(sp_s4_27) + (6029411367759/1000000000000 : ℝ)*(f.failure) + (13173898811193/1000000000000 : ℝ)*(f.sum) + (104913446897550193/418485466250000000000000000000 : ℝ)*base63 + (202181706909149/550675000000000000000000000 : ℝ)*base65 + (78000669851099/759950000000000000000000000 : ℝ)*base66 + (71107013888901/137668750000000000000000000 : ℝ)*base69 + (139735435009225789/1355761850000000000000000000000 : ℝ)*base71 + (17945400838759/49240000000000000000000000 : ℝ)*base73 + (99138061406751/189987500000000000000000000 : ℝ)*base75 + (12043234993969/30775000000000000000000000 : ℝ)*base77 + (1533367267286049651/3741993800000000000000000000000 : ℝ)*base78 + (82527/100000000000000000 : ℝ)*base86 + (82527/100000000000000000 : ℝ)*base88 + (82527/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((1231/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1231/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45597/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(45597/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22027/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22027/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10481/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10481/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1247/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1247/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4851/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4851/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309053_s4 p hpa hpb X hX hprev3

#print axioms solution

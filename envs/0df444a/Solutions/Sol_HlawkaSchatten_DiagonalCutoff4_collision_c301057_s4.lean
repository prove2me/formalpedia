-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301057_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:34:36.625984+00:00
-- url     : https://prove2.me/submissions/ae47fec1-cfaf-451c-be1b-87b079a63a5c

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
theorem collision_support_c301057_s4_s4_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (136752299/400000000 : ℝ)*x 0 + (-3418701033/10000000000 : ℝ)*x 1 + (6093934797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136752299/400000000 : ℝ)^65 ≤ (24080774300313/100000000000000 : ℝ)^49 := by
    have hnat : (136752299 : ℕ)^65*100000000000000^49 ≤ 24080774300313^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136752299 400000000 24080774300313 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3418701033/10000000000 : ℝ)^65 ≤ (24079779756551/100000000000000 : ℝ)^49 := by
    have hnat : (3418701033 : ℕ)^65*100000000000000^49 ≤ 24079779756551^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3418701033 10000000000 24079779756551 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6093934797/10000000000 : ℝ)^65 ≤ (323996537063/625000000000 : ℝ)^49 := by
    have hnat : (6093934797 : ℕ)^65*625000000000^49 ≤ 323996537063^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6093934797 10000000000 323996537063 625000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136752299/400000000 : ℝ), (-3418701033/10000000000 : ℝ), (6093934797/10000000000 : ℝ)] ![(24080774300313/100000000000000 : ℝ), (24079779756551/100000000000000 : ℝ), (323996537063/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136752299/400000000 : ℝ)|^65 ≤ (24080774300313/100000000000000 : ℝ)^49
        have hw : |(136752299/400000000 : ℝ)|=(136752299/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3418701033/10000000000 : ℝ)|^65 ≤ (24079779756551/100000000000000 : ℝ)^49
        have hw : |(-3418701033/10000000000 : ℝ)|=(3418701033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6093934797/10000000000 : ℝ)|^65 ≤ (323996537063/625000000000 : ℝ)^49
        have hw : |(6093934797/10000000000 : ℝ)|=(6093934797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s4_s4_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4644002911/10000000000 : ℝ)*x 0 + (7430599/16000000 : ℝ)*x 1 + (379902713/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4644002911/10000000000 : ℝ)^65 ≤ (9037799253261/25000000000000 : ℝ)^49 := by
    have hnat : (4644002911 : ℕ)^65*25000000000000^49 ≤ 9037799253261^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4644002911 10000000000 9037799253261 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7430599/16000000 : ℝ)^65 ≤ (4519056412501/12500000000000 : ℝ)^49 := by
    have hnat : (7430599 : ℕ)^65*12500000000000^49 ≤ 4519056412501^49*16000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7430599 16000000 4519056412501 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (379902713/1000000000 : ℝ)^65 ≤ (13848175829791/50000000000000 : ℝ)^49 := by
    have hnat : (379902713 : ℕ)^65*50000000000000^49 ≤ 13848175829791^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379902713 1000000000 13848175829791 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4644002911/10000000000 : ℝ), (7430599/16000000 : ℝ), (379902713/1000000000 : ℝ)] ![(9037799253261/25000000000000 : ℝ), (4519056412501/12500000000000 : ℝ), (13848175829791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4644002911/10000000000 : ℝ)|^65 ≤ (9037799253261/25000000000000 : ℝ)^49
        have hw : |(4644002911/10000000000 : ℝ)|=(4644002911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7430599/16000000 : ℝ)|^65 ≤ (4519056412501/12500000000000 : ℝ)^49
        have hw : |(7430599/16000000 : ℝ)|=(7430599/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(379902713/1000000000 : ℝ)|^65 ≤ (13848175829791/50000000000000 : ℝ)^49
        have hw : |(379902713/1000000000 : ℝ)|=(379902713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s4_s4_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3107632091/10000000000 : ℝ)*x 0 + (2725608559/10000000000 : ℝ)*x 1 + (3442650923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3107632091/10000000000 : ℝ)^65 ≤ (21217407782643/100000000000000 : ℝ)^49 := by
    have hnat : (3107632091 : ℕ)^65*100000000000000^49 ≤ 21217407782643^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3107632091 10000000000 21217407782643 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725608559/10000000000 : ℝ)^65 ≤ (17828919753051/100000000000000 : ℝ)^49 := by
    have hnat : (2725608559 : ℕ)^65*100000000000000^49 ≤ 17828919753051^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725608559 10000000000 17828919753051 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3442650923/5000000000 : ℝ)^65 ≤ (60953672446889/100000000000000 : ℝ)^49 := by
    have hnat : (3442650923 : ℕ)^65*100000000000000^49 ≤ 60953672446889^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3442650923 5000000000 60953672446889 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3107632091/10000000000 : ℝ), (2725608559/10000000000 : ℝ), (3442650923/5000000000 : ℝ)] ![(21217407782643/100000000000000 : ℝ), (17828919753051/100000000000000 : ℝ), (60953672446889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3107632091/10000000000 : ℝ)|^65 ≤ (21217407782643/100000000000000 : ℝ)^49
        have hw : |(-3107632091/10000000000 : ℝ)|=(3107632091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725608559/10000000000 : ℝ)|^65 ≤ (17828919753051/100000000000000 : ℝ)^49
        have hw : |(2725608559/10000000000 : ℝ)|=(2725608559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3442650923/5000000000 : ℝ)|^65 ≤ (60953672446889/100000000000000 : ℝ)^49
        have hw : |(3442650923/5000000000 : ℝ)|=(3442650923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s4_s4_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1553764237/5000000000 : ℝ)*x 0 + (-34068971/125000000 : ℝ)*x 1 + (1721362227/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1553764237/5000000000 : ℝ)^65 ≤ (4243293867603/20000000000000 : ℝ)^49 := by
    have hnat : (1553764237 : ℕ)^65*20000000000000^49 ≤ 4243293867603^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553764237 5000000000 4243293867603 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34068971/125000000 : ℝ)^65 ≤ (1782813118351/10000000000000 : ℝ)^49 := by
    have hnat : (34068971 : ℕ)^65*10000000000000^49 ≤ 1782813118351^49*125000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34068971 125000000 1782813118351 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1721362227/2500000000 : ℝ)^65 ≤ (60955399462057/100000000000000 : ℝ)^49 := by
    have hnat : (1721362227 : ℕ)^65*100000000000000^49 ≤ 60955399462057^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1721362227 2500000000 60955399462057 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1553764237/5000000000 : ℝ), (-34068971/125000000 : ℝ), (1721362227/2500000000 : ℝ)] ![(4243293867603/20000000000000 : ℝ), (1782813118351/10000000000000 : ℝ), (60955399462057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1553764237/5000000000 : ℝ)|^65 ≤ (4243293867603/20000000000000 : ℝ)^49
        have hw : |(1553764237/5000000000 : ℝ)|=(1553764237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34068971/125000000 : ℝ)|^65 ≤ (1782813118351/10000000000000 : ℝ)^49
        have hw : |(-34068971/125000000 : ℝ)|=(34068971/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1721362227/2500000000 : ℝ)|^65 ≤ (60955399462057/100000000000000 : ℝ)^49
        have hw : |(1721362227/2500000000 : ℝ)|=(1721362227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s4_s4_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (258024553/500000000 : ℝ)*x 0 + (830453939/1250000000 : ℝ)*x 1 + (-60903711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258024553/500000000 : ℝ)^65 ≤ (8315834773893/20000000000000 : ℝ)^49 := by
    have hnat : (258024553 : ℕ)^65*20000000000000^49 ≤ 8315834773893^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258024553 500000000 8315834773893 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (830453939/1250000000 : ℝ)^65 ≤ (58132032466333/100000000000000 : ℝ)^49 := by
    have hnat : (830453939 : ℕ)^65*100000000000000^49 ≤ 58132032466333^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830453939 1250000000 58132032466333 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60903711/5000000000 : ℝ)^65 ≤ (36099205419/12500000000000 : ℝ)^49 := by
    have hnat : (60903711 : ℕ)^65*12500000000000^49 ≤ 36099205419^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60903711 5000000000 36099205419 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258024553/500000000 : ℝ), (830453939/1250000000 : ℝ), (-60903711/5000000000 : ℝ)] ![(8315834773893/20000000000000 : ℝ), (58132032466333/100000000000000 : ℝ), (36099205419/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258024553/500000000 : ℝ)|^65 ≤ (8315834773893/20000000000000 : ℝ)^49
        have hw : |(258024553/500000000 : ℝ)|=(258024553/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(830453939/1250000000 : ℝ)|^65 ≤ (58132032466333/100000000000000 : ℝ)^49
        have hw : |(830453939/1250000000 : ℝ)|=(830453939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-60903711/5000000000 : ℝ)|^65 ≤ (36099205419/12500000000000 : ℝ)^49
        have hw : |(-60903711/5000000000 : ℝ)|=(60903711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s4_s4_12 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (22904477/50000000 : ℝ)*x 0 + (5897458339/10000000000 : ℝ)*x 1 + (2376503991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22904477/50000000 : ℝ)^65 ≤ (35500976060061/100000000000000 : ℝ)^49 := by
    have hnat : (22904477 : ℕ)^65*100000000000000^49 ≤ 35500976060061^49*50000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22904477 50000000 35500976060061 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5897458339/10000000000 : ℝ)^65 ≤ (49634076415643/100000000000000 : ℝ)^49 := by
    have hnat : (5897458339 : ℕ)^65*100000000000000^49 ≤ 49634076415643^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5897458339 10000000000 49634076415643 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2376503991/10000000000 : ℝ)^65 ≤ (232264804823/1562500000000 : ℝ)^49 := by
    have hnat : (2376503991 : ℕ)^65*1562500000000^49 ≤ 232264804823^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2376503991 10000000000 232264804823 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(22904477/50000000 : ℝ), (5897458339/10000000000 : ℝ), (2376503991/10000000000 : ℝ)] ![(35500976060061/100000000000000 : ℝ), (49634076415643/100000000000000 : ℝ), (232264804823/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(22904477/50000000 : ℝ)|^65 ≤ (35500976060061/100000000000000 : ℝ)^49
        have hw : |(22904477/50000000 : ℝ)|=(22904477/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5897458339/10000000000 : ℝ)|^65 ≤ (49634076415643/100000000000000 : ℝ)^49
        have hw : |(5897458339/10000000000 : ℝ)|=(5897458339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2376503991/10000000000 : ℝ)|^65 ≤ (232264804823/1562500000000 : ℝ)^49
        have hw : |(2376503991/10000000000 : ℝ)|=(2376503991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s4_s4_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-545142773/2000000000 : ℝ)*x 0 + (1553765497/5000000000 : ℝ)*x 1 + (1377060401/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545142773/2000000000 : ℝ)^65 ≤ (8914916759193/50000000000000 : ℝ)^49 := by
    have hnat : (545142773 : ℕ)^65*50000000000000^49 ≤ 8914916759193^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545142773 2000000000 8914916759193 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1553765497/5000000000 : ℝ)^65 ≤ (1060824608059/5000000000000 : ℝ)^49 := by
    have hnat : (1553765497 : ℕ)^65*5000000000000^49 ≤ 1060824608059^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553765497 5000000000 1060824608059 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1377060401/2000000000 : ℝ)^65 ≤ (60953674314091/100000000000000 : ℝ)^49 := by
    have hnat : (1377060401 : ℕ)^65*100000000000000^49 ≤ 60953674314091^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377060401 2000000000 60953674314091 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-545142773/2000000000 : ℝ), (1553765497/5000000000 : ℝ), (1377060401/2000000000 : ℝ)] ![(8914916759193/50000000000000 : ℝ), (1060824608059/5000000000000 : ℝ), (60953674314091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-545142773/2000000000 : ℝ)|^65 ≤ (8914916759193/50000000000000 : ℝ)^49
        have hw : |(-545142773/2000000000 : ℝ)|=(545142773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1553765497/5000000000 : ℝ)|^65 ≤ (1060824608059/5000000000000 : ℝ)^49
        have hw : |(1553765497/5000000000 : ℝ)|=(1553765497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1377060401/2000000000 : ℝ)|^65 ≤ (60953674314091/100000000000000 : ℝ)^49
        have hw : |(1377060401/2000000000 : ℝ)|=(1377060401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s4_s4_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (136281159/500000000 : ℝ)*x 0 + (-1553713803/5000000000 : ℝ)*x 1 + (6885448747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136281159/500000000 : ℝ)^65 ≤ (8914523311137/50000000000000 : ℝ)^49 := by
    have hnat : (136281159 : ℕ)^65*50000000000000^49 ≤ 8914523311137^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136281159 500000000 8914523311137 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1553713803/5000000000 : ℝ)^65 ≤ (2121555580051/10000000000000 : ℝ)^49 := by
    have hnat : (1553713803 : ℕ)^65*10000000000000^49 ≤ 2121555580051^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553713803 5000000000 2121555580051 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6885448747/10000000000 : ℝ)^65 ≤ (12191079514271/20000000000000 : ℝ)^49 := by
    have hnat : (6885448747 : ℕ)^65*20000000000000^49 ≤ 12191079514271^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6885448747 10000000000 12191079514271 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136281159/500000000 : ℝ), (-1553713803/5000000000 : ℝ), (6885448747/10000000000 : ℝ)] ![(8914523311137/50000000000000 : ℝ), (2121555580051/10000000000000 : ℝ), (12191079514271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136281159/500000000 : ℝ)|^65 ≤ (8914523311137/50000000000000 : ℝ)^49
        have hw : |(136281159/500000000 : ℝ)|=(136281159/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1553713803/5000000000 : ℝ)|^65 ≤ (2121555580051/10000000000000 : ℝ)^49
        have hw : |(-1553713803/5000000000 : ℝ)|=(1553713803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6885448747/10000000000 : ℝ)|^65 ≤ (12191079514271/20000000000000 : ℝ)^49
        have hw : |(6885448747/10000000000 : ℝ)|=(6885448747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s4_s4_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6643486559/10000000000 : ℝ)*x 0 + (5160648591/10000000000 : ℝ)*x 1 + (-121807033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6643486559/10000000000 : ℝ)^65 ≤ (58130349974717/100000000000000 : ℝ)^49 := by
    have hnat : (6643486559 : ℕ)^65*100000000000000^49 ≤ 58130349974717^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6643486559 10000000000 58130349974717 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5160648591/10000000000 : ℝ)^65 ≤ (20790428795559/50000000000000 : ℝ)^49 := by
    have hnat : (5160648591 : ℕ)^65*50000000000000^49 ≤ 20790428795559^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5160648591 10000000000 20790428795559 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121807033/10000000000 : ℝ)^65 ≤ (144396209959/50000000000000 : ℝ)^49 := by
    have hnat : (121807033 : ℕ)^65*50000000000000^49 ≤ 144396209959^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121807033 10000000000 144396209959 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6643486559/10000000000 : ℝ), (5160648591/10000000000 : ℝ), (-121807033/10000000000 : ℝ)] ![(58130349974717/100000000000000 : ℝ), (20790428795559/50000000000000 : ℝ), (144396209959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6643486559/10000000000 : ℝ)|^65 ≤ (58130349974717/100000000000000 : ℝ)^49
        have hw : |(6643486559/10000000000 : ℝ)|=(6643486559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5160648591/10000000000 : ℝ)|^65 ≤ (20790428795559/50000000000000 : ℝ)^49
        have hw : |(5160648591/10000000000 : ℝ)|=(5160648591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-121807033/10000000000 : ℝ)|^65 ≤ (144396209959/50000000000000 : ℝ)^49
        have hw : |(-121807033/10000000000 : ℝ)|=(121807033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s4_s4_18 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2948664929/5000000000 : ℝ)*x 0 + (4581035387/10000000000 : ℝ)*x 1 + (2376503421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2948664929/5000000000 : ℝ)^65 ≤ (193877507881/390625000000 : ℝ)^49 := by
    have hnat : (2948664929 : ℕ)^65*390625000000^49 ≤ 193877507881^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2948664929 5000000000 193877507881 390625000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4581035387/10000000000 : ℝ)^65 ≤ (17751207590129/50000000000000 : ℝ)^49 := by
    have hnat : (4581035387 : ℕ)^65*50000000000000^49 ≤ 17751207590129^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4581035387 10000000000 17751207590129 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2376503421/10000000000 : ℝ)^65 ≤ (14864942779153/100000000000000 : ℝ)^49 := by
    have hnat : (2376503421 : ℕ)^65*100000000000000^49 ≤ 14864942779153^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2376503421 10000000000 14864942779153 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2948664929/5000000000 : ℝ), (4581035387/10000000000 : ℝ), (2376503421/10000000000 : ℝ)] ![(193877507881/390625000000 : ℝ), (17751207590129/50000000000000 : ℝ), (14864942779153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2948664929/5000000000 : ℝ)|^65 ≤ (193877507881/390625000000 : ℝ)^49
        have hw : |(2948664929/5000000000 : ℝ)|=(2948664929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4581035387/10000000000 : ℝ)|^65 ≤ (17751207590129/50000000000000 : ℝ)^49
        have hw : |(4581035387/10000000000 : ℝ)|=(4581035387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2376503421/10000000000 : ℝ)|^65 ≤ (14864942779153/100000000000000 : ℝ)^49
        have hw : |(2376503421/10000000000 : ℝ)|=(2376503421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s4_s4_19 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4076628537/10000000000 : ℝ)*x 0 + (1417088687/5000000000 : ℝ)*x 1 + (6002519157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4076628537/10000000000 : ℝ)^65 ≤ (6082505757397/20000000000000 : ℝ)^49 := by
    have hnat : (4076628537 : ℕ)^65*20000000000000^49 ≤ 6082505757397^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4076628537 10000000000 6082505757397 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1417088687/5000000000 : ℝ)^65 ≤ (9388532039947/50000000000000 : ℝ)^49 := by
    have hnat : (1417088687 : ℕ)^65*50000000000000^49 ≤ 9388532039947^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1417088687 5000000000 9388532039947 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6002519157/10000000000 : ℝ)^65 ≤ (50810407118197/100000000000000 : ℝ)^49 := by
    have hnat : (6002519157 : ℕ)^65*100000000000000^49 ≤ 50810407118197^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6002519157 10000000000 50810407118197 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4076628537/10000000000 : ℝ), (1417088687/5000000000 : ℝ), (6002519157/10000000000 : ℝ)] ![(6082505757397/20000000000000 : ℝ), (9388532039947/50000000000000 : ℝ), (50810407118197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4076628537/10000000000 : ℝ)|^65 ≤ (6082505757397/20000000000000 : ℝ)^49
        have hw : |(-4076628537/10000000000 : ℝ)|=(4076628537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1417088687/5000000000 : ℝ)|^65 ≤ (9388532039947/50000000000000 : ℝ)^49
        have hw : |(1417088687/5000000000 : ℝ)|=(1417088687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6002519157/10000000000 : ℝ)|^65 ≤ (50810407118197/100000000000000 : ℝ)^49
        have hw : |(6002519157/10000000000 : ℝ)|=(6002519157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s4_s4_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (283420257/1000000000 : ℝ)*x 0 + (-163057593/400000000 : ℝ)*x 1 + (24010663/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (283420257/1000000000 : ℝ)^65 ≤ (18777285516883/100000000000000 : ℝ)^49 := by
    have hnat : (283420257 : ℕ)^65*100000000000000^49 ≤ 18777285516883^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283420257 1000000000 18777285516883 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163057593/400000000 : ℝ)^65 ≤ (30410661268521/100000000000000 : ℝ)^49 := by
    have hnat : (163057593 : ℕ)^65*100000000000000^49 ≤ 30410661268521^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163057593 400000000 30410661268521 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24010663/40000000 : ℝ)^65 ≤ (50812053199799/100000000000000 : ℝ)^49 := by
    have hnat : (24010663 : ℕ)^65*100000000000000^49 ≤ 50812053199799^49*40000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24010663 40000000 50812053199799 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(283420257/1000000000 : ℝ), (-163057593/400000000 : ℝ), (24010663/40000000 : ℝ)] ![(18777285516883/100000000000000 : ℝ), (30410661268521/100000000000000 : ℝ), (50812053199799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(283420257/1000000000 : ℝ)|^65 ≤ (18777285516883/100000000000000 : ℝ)^49
        have hw : |(283420257/1000000000 : ℝ)|=(283420257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-163057593/400000000 : ℝ)|^65 ≤ (30410661268521/100000000000000 : ℝ)^49
        have hw : |(-163057593/400000000 : ℝ)|=(163057593/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(24010663/40000000 : ℝ)|^65 ≤ (50812053199799/100000000000000 : ℝ)^49
        have hw : |(24010663/40000000 : ℝ)|=(24010663/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s4_s4_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6147585433/10000000000 : ℝ)*x 0 + (5425250523/10000000000 : ℝ)*x 1 + (-366429707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6147585433/10000000000 : ℝ)^65 ≤ (52445731551743/100000000000000 : ℝ)^49 := by
    have hnat : (6147585433 : ℕ)^65*100000000000000^49 ≤ 52445731551743^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6147585433 10000000000 52445731551743 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425250523/10000000000 : ℝ)^65 ≤ (44432395829793/100000000000000 : ℝ)^49 := by
    have hnat : (5425250523 : ℕ)^65*100000000000000^49 ≤ 44432395829793^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425250523 10000000000 44432395829793 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (366429707/5000000000 : ℝ)^65 ≤ (1560936299147/50000000000000 : ℝ)^49 := by
    have hnat : (366429707 : ℕ)^65*50000000000000^49 ≤ 1560936299147^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366429707 5000000000 1560936299147 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6147585433/10000000000 : ℝ), (5425250523/10000000000 : ℝ), (-366429707/5000000000 : ℝ)] ![(52445731551743/100000000000000 : ℝ), (44432395829793/100000000000000 : ℝ), (1560936299147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6147585433/10000000000 : ℝ)|^65 ≤ (52445731551743/100000000000000 : ℝ)^49
        have hw : |(6147585433/10000000000 : ℝ)|=(6147585433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425250523/10000000000 : ℝ)|^65 ≤ (44432395829793/100000000000000 : ℝ)^49
        have hw : |(5425250523/10000000000 : ℝ)|=(5425250523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-366429707/5000000000 : ℝ)|^65 ≤ (1560936299147/50000000000000 : ℝ)^49
        have hw : |(-366429707/5000000000 : ℝ)|=(366429707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s4_s4_25 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (796085909/2000000000 : ℝ)*x 0 + (5425250523/10000000000 : ℝ)*x 1 + (908278963/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (796085909/2000000000 : ℝ)^65 ≤ (14732105634441/50000000000000 : ℝ)^49 := by
    have hnat : (796085909 : ℕ)^65*50000000000000^49 ≤ 14732105634441^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796085909 2000000000 14732105634441 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425250523/10000000000 : ℝ)^65 ≤ (44432395829793/100000000000000 : ℝ)^49 := by
    have hnat : (5425250523 : ℕ)^65*100000000000000^49 ≤ 44432395829793^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425250523 10000000000 44432395829793 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (908278963/2500000000 : ℝ)^65 ≤ (6525848220703/25000000000000 : ℝ)^49 := by
    have hnat : (908278963 : ℕ)^65*25000000000000^49 ≤ 6525848220703^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908278963 2500000000 6525848220703 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(796085909/2000000000 : ℝ), (5425250523/10000000000 : ℝ), (908278963/2500000000 : ℝ)] ![(14732105634441/50000000000000 : ℝ), (44432395829793/100000000000000 : ℝ), (6525848220703/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(796085909/2000000000 : ℝ)|^65 ≤ (14732105634441/50000000000000 : ℝ)^49
        have hw : |(796085909/2000000000 : ℝ)|=(796085909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425250523/10000000000 : ℝ)|^65 ≤ (44432395829793/100000000000000 : ℝ)^49
        have hw : |(5425250523/10000000000 : ℝ)|=(5425250523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(908278963/2500000000 : ℝ)|^65 ≤ (6525848220703/25000000000000 : ℝ)^49
        have hw : |(908278963/2500000000 : ℝ)|=(908278963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301057_s4 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((36217/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36217/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2897/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2897/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3713/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3713/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((23833/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23833/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9533/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9533/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1233/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1233/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s4_pow0 : (36217/50000 : ℝ) ^ (129/32 : ℝ) ≤ (2725166723625038483/10000000000000000000 : ℝ) := by
    have hpowers : (36217/50000 : ℝ)^129 ≤ (2725166723625038483/10000000000000000000 : ℝ)^32 := by
      have hnat : (36217 : ℕ)^129*10000000000000000000^32 ≤ 2725166723625038483^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36217 50000 2725166723625038483 10000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36217/50000 : ℝ)) (X := (2725166723625038483/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner0a : (12725166723625038483/10000000000000000000 : ℝ) ≤ (5308025962540183/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (12725166723625038483/10000000000000000000 : ℝ)^32 ≤ (5308025962540183/5000000000000000 : ℝ)^129 := by
      have hnat : (12725166723625038483 : ℕ)^32*5000000000000000^129 ≤ 5308025962540183^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12725166723625038483 10000000000000000000 5308025962540183 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5308025962540183/5000000000000000 : ℝ)) (X := (12725166723625038483/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner0b : (7725166723625038483/5000000000000000000 : ℝ) ≤ (5569783443674733/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (7725166723625038483/5000000000000000000 : ℝ)^32 ≤ (5569783443674733/5000000000000000 : ℝ)^129 := by
      have hnat : (7725166723625038483 : ℕ)^32*5000000000000000^129 ≤ 5569783443674733^129*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7725166723625038483 5000000000000000000 5569783443674733 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5569783443674733/5000000000000000 : ℝ)) (X := (7725166723625038483/5000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(308025962540183/3621700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(5235149622691/72434000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (36217/50000 : ℝ)) (alpha := (308025962540183/3621700000000000 : ℝ)) (beta := (5235149622691/72434000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (36217/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(308025962540183/3621700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(5235149622691/72434000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (2897/4000 : ℝ) ^ (129/32 : ℝ) ≤ (27238019800336827769/100000000000000000000 : ℝ) := by
    have hpowers : (2897/4000 : ℝ)^129 ≤ (27238019800336827769/100000000000000000000 : ℝ)^32 := by
      have hnat : (2897 : ℕ)^129*100000000000000000000^32 ≤ 27238019800336827769^32*4000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2897 4000 27238019800336827769 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2897/4000 : ℝ)) (X := (27238019800336827769/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner1a : (127238019800336827769/100000000000000000000 : ℝ) ≤ (21231538967307/20000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (127238019800336827769/100000000000000000000 : ℝ)^32 ≤ (21231538967307/20000000000000 : ℝ)^129 := by
      have hnat : (127238019800336827769 : ℕ)^32*20000000000000^129 ≤ 21231538967307^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127238019800336827769 100000000000000000000 21231538967307 20000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (21231538967307/20000000000000 : ℝ)) (X := (127238019800336827769/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner1b : (77238019800336827769/50000000000000000000 : ℝ) ≤ (5569539342073633/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (77238019800336827769/50000000000000000000 : ℝ)^32 ≤ (5569539342073633/5000000000000000 : ℝ)^129 := by
      have hnat : (77238019800336827769 : ℕ)^32*5000000000000000^129 ≤ 5569539342073633^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77238019800336827769 50000000000000000000 5569539342073633 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5569539342073633/5000000000000000 : ℝ)) (X := (77238019800336827769/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1231538967307/14485000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(261654600246883/3621250000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (2897/4000 : ℝ)) (alpha := (1231538967307/14485000000000 : ℝ)) (beta := (261654600246883/3621250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (2897/4000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1231538967307/14485000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(261654600246883/3621250000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (3713/20000 : ℝ) ^ (129/32 : ℝ) ≤ (56350339364083799/50000000000000000000 : ℝ) := by
    have hpowers : (3713/20000 : ℝ)^129 ≤ (56350339364083799/50000000000000000000 : ℝ)^32 := by
      have hnat : (3713 : ℕ)^129*50000000000000000000^32 ≤ 56350339364083799^32*20000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3713 20000 56350339364083799 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3713/20000 : ℝ)) (X := (56350339364083799/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner2a : (50056350339364083799/50000000000000000000 : ℝ) ≤ (2500698622986949/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (50056350339364083799/50000000000000000000 : ℝ)^32 ≤ (2500698622986949/2500000000000000 : ℝ)^129 := by
      have hnat : (50056350339364083799 : ℕ)^32*2500000000000000^129 ≤ 2500698622986949^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50056350339364083799 50000000000000000000 2500698622986949 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500698622986949/2500000000000000 : ℝ)) (X := (50056350339364083799/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner2b : (25056350339364083799/25000000000000000000 : ℝ) ≤ (10005586619399677/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (25056350339364083799/25000000000000000000 : ℝ)^32 ≤ (10005586619399677/10000000000000000 : ℝ)^129 := by
      have hnat : (25056350339364083799 : ℕ)^32*10000000000000000^129 ≤ 10005586619399677^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25056350339364083799 25000000000000000000 10005586619399677 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005586619399677/10000000000000000 : ℝ)) (X := (25056350339364083799/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(698622986949/464125000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(2792127451881/1856500000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (3713/20000 : ℝ)) (alpha := (698622986949/464125000000000 : ℝ)) (beta := (2792127451881/1856500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (3713/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(698622986949/464125000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(2792127451881/1856500000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_1 : ((136752299/400000000 : ℝ)*X 1 0+(-3418701033/10000000000 : ℝ)*X 1 1+(6093934797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((4644002911/10000000000 : ℝ)*X 0 0+(7430599/16000000 : ℝ)*X 0 1+(379902713/1000000000 : ℝ)*X 0 2+(4644002911/10000000000 : ℝ)*X 1 0+(7430599/16000000 : ℝ)*X 1 1+(379902713/1000000000 : ℝ)*X 1 2+(4644002911/10000000000 : ℝ)*X 2 0+(7430599/16000000 : ℝ)*X 2 1+(379902713/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-3107632091/10000000000 : ℝ)*X 0 0+(2725608559/10000000000 : ℝ)*X 0 1+(3442650923/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((1553764237/5000000000 : ℝ)*X 1 0+(-34068971/125000000 : ℝ)*X 1 1+(1721362227/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((258024553/500000000 : ℝ)*X 2 0+(830453939/1250000000 : ℝ)*X 2 1+(-60903711/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_12 : ((22904477/50000000 : ℝ)*X 0 0+(5897458339/10000000000 : ℝ)*X 0 1+(2376503991/10000000000 : ℝ)*X 0 2+(22904477/50000000 : ℝ)*X 1 0+(5897458339/10000000000 : ℝ)*X 1 1+(2376503991/10000000000 : ℝ)*X 1 2+(22904477/50000000 : ℝ)*X 2 0+(5897458339/10000000000 : ℝ)*X 2 1+(2376503991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s4_s4_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((-545142773/2000000000 : ℝ)*X 0 0+(1553765497/5000000000 : ℝ)*X 0 1+(1377060401/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s4_s4_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((136281159/500000000 : ℝ)*X 1 0+(-1553713803/5000000000 : ℝ)*X 1 1+(6885448747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s4_s4_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((6643486559/10000000000 : ℝ)*X 2 0+(5160648591/10000000000 : ℝ)*X 2 1+(-121807033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s4_s4_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_18 : ((2948664929/5000000000 : ℝ)*X 0 0+(4581035387/10000000000 : ℝ)*X 0 1+(2376503421/10000000000 : ℝ)*X 0 2+(2948664929/5000000000 : ℝ)*X 1 0+(4581035387/10000000000 : ℝ)*X 1 1+(2376503421/10000000000 : ℝ)*X 1 2+(2948664929/5000000000 : ℝ)*X 2 0+(4581035387/10000000000 : ℝ)*X 2 1+(2376503421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s4_s4_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_19 : ((-4076628537/10000000000 : ℝ)*X 0 0+(1417088687/5000000000 : ℝ)*X 0 1+(6002519157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s4_s4_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((283420257/1000000000 : ℝ)*X 1 0+(-163057593/400000000 : ℝ)*X 1 1+(24010663/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s4_s4_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((6147585433/10000000000 : ℝ)*X 2 0+(5425250523/10000000000 : ℝ)*X 2 1+(-366429707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s4_s4_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_25 : ((796085909/2000000000 : ℝ)*X 0 0+(5425250523/10000000000 : ℝ)*X 0 1+(908278963/2500000000 : ℝ)*X 0 2+(796085909/2000000000 : ℝ)*X 1 0+(5425250523/10000000000 : ℝ)*X 1 1+(908278963/2500000000 : ℝ)*X 1 2+(796085909/2000000000 : ℝ)*X 2 0+(5425250523/10000000000 : ℝ)*X 2 1+(908278963/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s4_s4_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((23833/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23833/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1268447116753440958187479323/152175925678515625000000000000000 : ℝ) := by norm_num
    linear_combination (713749/250000000000 : ℝ)*(base23) + (912309/500000000000 : ℝ)*(base39) + (402243/250000000000 : ℝ)*(base49) + (109771734371/50000000000 : ℝ)*(base59) + (958844843451/1000000000000 : ℝ)*(base60) + (1293776425549/250000000000 : ℝ)*(major_s4_0) + (1293776425549/250000000000 : ℝ)*(major_s4_1) + (1293776425549/250000000000 : ℝ)*(major_s4_2) + (1370323564807/200000000000 : ℝ)*(sp_s4_7) + (6851719062229/1000000000000 : ℝ)*(sp_s4_8) + (6851716207233/1000000000000 : ℝ)*(sp_s4_9) + (1749231132661/500000000000 : ℝ)*(sp_s4_12) + (50619097/500000000000 : ℝ)*(sp_s4_13) + (2729837/100000000000 : ℝ)*(sp_s4_25) + (874622390923/250000000000 : ℝ)*(f.failure) + (6851719062229/1000000000000 : ℝ)*(f.sum) + (522691671257057751/2689140250000000000000000000000 : ℝ)*base62 + (789263548479737/928250000000000000000000000 : ℝ)*base65 + (627672990937909/1810625000000000000000000000 : ℝ)*base67 + (74872014208427/232062500000000000000000000 : ℝ)*base68 + (1991209165931047229/2101151890625000000000000000000 : ℝ)*base71 + (108123648772639/181085000000000000000000000 : ℝ)*base72 + (484831921183/14485000000000000000000000 : ℝ)*base74 + (2649037400003/905425000000000000000000000 : ℝ)*base76 + (243580701510461593/16393851406250000000000000000000 : ℝ)*base78 + (1537/6250000000000000 : ℝ)*base86 + (1537/6250000000000000 : ℝ)*base88 + (1537/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9533/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9533/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (150223904492771056621976631/16809215125000000000000000000000 : ℝ) := by norm_num
    linear_combination (5027983/500000000000 : ℝ)*(base21) + (451/125000000000 : ℝ)*(base40) + (2195427971261/1000000000000 : ℝ)*(base59) + (618309563769/500000000000 : ℝ)*(base60) + (1293772769509/250000000000 : ℝ)*(major_s4_0) + (1293772769509/250000000000 : ℝ)*(major_s4_1) + (1293772769509/250000000000 : ℝ)*(major_s4_2) + (14410451/1000000000000 : ℝ)*(sp_s4_6) + (25098177/250000000000 : ℝ)*(sp_s4_7) + (1370319821387/200000000000 : ℝ)*(sp_s4_13) + (6851699499643/1000000000000 : ℝ)*(sp_s4_14) + (6851653210343/1000000000000 : ℝ)*(sp_s4_15) + (139938610679/40000000000 : ℝ)*(sp_s4_18) + (18116667/500000000000 : ℝ)*(sp_s4_21) + (1749239838713/500000000000 : ℝ)*(f.failure) + (6851699499643/1000000000000 : ℝ)*(f.sum) + (5233967290503881/42017816406250000000000000000 : ℝ)*base63 + (165561993424121/464125000000000000000000000 : ℝ)*base65 + (4600708381971/28291015625000000000000000 : ℝ)*base67 + (186807790604097/928250000000000000000000000 : ℝ)*base69 + (4317783975486823531/8404607562500000000000000000000 : ℝ)*base71 + (8058030886031/181085000000000000000000000 : ℝ)*base72 + (1113976548793/14485000000000000000000000 : ℝ)*base74 + (1090429035598469/1810850000000000000000000000 : ℝ)*base77 + (7322354142029920127/65575405625000000000000000000000 : ℝ)*base78 + (4547/12500000000000000 : ℝ)*base86 + (4547/12500000000000000 : ℝ)*base88 + (4547/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1233/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1233/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (65153178225587323760892011637/9739259243425000000000000000000000 : ℝ) := by norm_num
    linear_combination (3240797193/125000000000 : ℝ)*(base5) + (789677/500000000000 : ℝ)*(base40) + (1546829/1000000000000 : ℝ)*(base50) + (730821965697/1000000000000 : ℝ)*(base59) + (111775587257/40000000000 : ℝ)*(major_s4_0) + (111775587257/40000000000 : ℝ)*(major_s4_1) + (111775587257/40000000000 : ℝ)*(major_s4_2) + (2690799/1000000000000 : ℝ)*(sp_s4_1) + (3227577/100000000000 : ℝ)*(sp_s4_9) + (2162253/50000000000 : ℝ)*(sp_s4_15) + (924926483311/250000000000 : ℝ)*(sp_s4_19) + (739940648489/200000000000 : ℝ)*(sp_s4_20) + (3725556789957/1000000000000 : ℝ)*(sp_s4_21) + (1863144822143/1000000000000 : ℝ)*(sp_s4_25) + (1889071199687/1000000000000 : ℝ)*(f.failure) + (924926483311/250000000000 : ℝ)*(f.sum) + (5056718493557519/107565610000000000000000000000 : ℝ)*base62 + (31272219833413/74260000000000000000000000 : ℝ)*base65 + (18128955674091/144850000000000000000000000 : ℝ)*base67 + (189055687549/2320625000000000000000000 : ℝ)*base69 + (46997261429799797/168092151250000000000000000000 : ℝ)*base71 + (27925004025481/181085000000000000000000000 : ℝ)*base73 + (9077391005359/14485000000000000000000000 : ℝ)*base75 + (87867527667631/144868000000000000000000000 : ℝ)*base77 + (8552607677772281/163938514062500000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (53/25000000000000000 : ℝ)*base86 + (53/25000000000000000 : ℝ)*base88 + (53/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((36217/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36217/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2897/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2897/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3713/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3713/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((23833/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23833/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9533/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9533/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1233/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1233/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301057_s4 p hpa hpb X hX hprev3

#print axioms solution

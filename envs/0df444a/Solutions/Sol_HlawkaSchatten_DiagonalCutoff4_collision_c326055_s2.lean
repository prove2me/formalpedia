-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c326055_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:10:52.55466+00:00
-- url     : https://prove2.me/submissions/5e0b442a-3da3-43e1-93bd-22a4e7733e21

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
theorem collision_support_c326055_s2_s2_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1918446979/10000000000 : ℝ)*x 0 + (5396385053/10000000000 : ℝ)*x 1 + (2333983557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1918446979/10000000000 : ℝ)^89 ≤ (1669929460269/12500000000000 : ℝ)^73 := by
    have hnat : (1918446979 : ℕ)^89*12500000000000^73 ≤ 1669929460269^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918446979 10000000000 1669929460269 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396385053/10000000000 : ℝ)^89 ≤ (47139586084873/100000000000000 : ℝ)^73 := by
    have hnat : (5396385053 : ℕ)^89*100000000000000^73 ≤ 47139586084873^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396385053 10000000000 47139586084873 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2333983557/5000000000 : ℝ)^89 ≤ (39500978221033/100000000000000 : ℝ)^73 := by
    have hnat : (2333983557 : ℕ)^89*100000000000000^73 ≤ 39500978221033^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2333983557 5000000000 39500978221033 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1918446979/10000000000 : ℝ), (5396385053/10000000000 : ℝ), (2333983557/5000000000 : ℝ)] ![(1669929460269/12500000000000 : ℝ), (47139586084873/100000000000000 : ℝ), (39500978221033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1918446979/10000000000 : ℝ)|^89 ≤ (1669929460269/12500000000000 : ℝ)^73
        have hw : |(-1918446979/10000000000 : ℝ)|=(1918446979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396385053/10000000000 : ℝ)|^89 ≤ (47139586084873/100000000000000 : ℝ)^73
        have hw : |(5396385053/10000000000 : ℝ)|=(5396385053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2333983557/5000000000 : ℝ)|^89 ≤ (39500978221033/100000000000000 : ℝ)^73
        have hw : |(2333983557/5000000000 : ℝ)|=(2333983557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s2_s2_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (233340471/500000000 : ℝ)*x 0 + (-37182543/312500000 : ℝ)*x 1 + (1486322531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (233340471/500000000 : ℝ)^89 ≤ (19744517393881/50000000000000 : ℝ)^73 := by
    have hnat : (233340471 : ℕ)^89*50000000000000^73 ≤ 19744517393881^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233340471 500000000 19744517393881 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37182543/312500000 : ℝ)^89 ≤ (373101107587/5000000000000 : ℝ)^73 := by
    have hnat : (37182543 : ℕ)^89*5000000000000^73 ≤ 373101107587^73*312500000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37182543 312500000 373101107587 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1486322531/2500000000 : ℝ)^89 ≤ (10609788608433/20000000000000 : ℝ)^73 := by
    have hnat : (1486322531 : ℕ)^89*20000000000000^73 ≤ 10609788608433^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1486322531 2500000000 10609788608433 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(233340471/500000000 : ℝ), (-37182543/312500000 : ℝ), (1486322531/2500000000 : ℝ)] ![(19744517393881/50000000000000 : ℝ), (373101107587/5000000000000 : ℝ), (10609788608433/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(233340471/500000000 : ℝ)|^89 ≤ (19744517393881/50000000000000 : ℝ)^73
        have hw : |(233340471/500000000 : ℝ)|=(233340471/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37182543/312500000 : ℝ)|^89 ≤ (373101107587/5000000000000 : ℝ)^73
        have hw : |(-37182543/312500000 : ℝ)|=(37182543/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1486322531/2500000000 : ℝ)|^89 ≤ (10609788608433/20000000000000 : ℝ)^73
        have hw : |(1486322531/2500000000 : ℝ)|=(1486322531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s2_s2_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4667911577/10000000000 : ℝ)*x 0 + (5396554391/10000000000 : ℝ)*x 1 + (-1918302043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4667911577/10000000000 : ℝ)^89 ≤ (19750202627379/50000000000000 : ℝ)^73 := by
    have hnat : (4667911577 : ℕ)^89*50000000000000^73 ≤ 19750202627379^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4667911577 10000000000 19750202627379 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396554391/10000000000 : ℝ)^89 ≤ (47141389542323/100000000000000 : ℝ)^73 := by
    have hnat : (5396554391 : ℕ)^89*100000000000000^73 ≤ 47141389542323^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396554391 10000000000 47141389542323 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1918302043/10000000000 : ℝ)^89 ≤ (13358205192021/100000000000000 : ℝ)^73 := by
    have hnat : (1918302043 : ℕ)^89*100000000000000^73 ≤ 13358205192021^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918302043 10000000000 13358205192021 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4667911577/10000000000 : ℝ), (5396554391/10000000000 : ℝ), (-1918302043/10000000000 : ℝ)] ![(19750202627379/50000000000000 : ℝ), (47141389542323/100000000000000 : ℝ), (13358205192021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4667911577/10000000000 : ℝ)|^89 ≤ (19750202627379/50000000000000 : ℝ)^73
        have hw : |(4667911577/10000000000 : ℝ)|=(4667911577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396554391/10000000000 : ℝ)|^89 ≤ (47141389542323/100000000000000 : ℝ)^73
        have hw : |(5396554391/10000000000 : ℝ)|=(5396554391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1918302043/10000000000 : ℝ)|^89 ≤ (13358205192021/100000000000000 : ℝ)^73
        have hw : |(-1918302043/10000000000 : ℝ)|=(1918302043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s2_s2_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3039487067/5000000000 : ℝ)*x 0 + (151936821/400000000 : ℝ)*x 1 + (1041560227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3039487067/5000000000 : ℝ)^89 ≤ (54506793486547/100000000000000 : ℝ)^73 := by
    have hnat : (3039487067 : ℕ)^89*100000000000000^73 ≤ 54506793486547^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3039487067 5000000000 54506793486547 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151936821/400000000 : ℝ)^89 ≤ (30722831958247/100000000000000 : ℝ)^73 := by
    have hnat : (151936821 : ℕ)^89*100000000000000^73 ≤ 30722831958247^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151936821 400000000 30722831958247 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041560227/5000000000 : ℝ)^89 ≤ (14770374548753/100000000000000 : ℝ)^73 := by
    have hnat : (1041560227 : ℕ)^89*100000000000000^73 ≤ 14770374548753^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041560227 5000000000 14770374548753 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3039487067/5000000000 : ℝ), (151936821/400000000 : ℝ), (1041560227/5000000000 : ℝ)] ![(54506793486547/100000000000000 : ℝ), (30722831958247/100000000000000 : ℝ), (14770374548753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3039487067/5000000000 : ℝ)|^89 ≤ (54506793486547/100000000000000 : ℝ)^73
        have hw : |(3039487067/5000000000 : ℝ)|=(3039487067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(151936821/400000000 : ℝ)|^89 ≤ (30722831958247/100000000000000 : ℝ)^73
        have hw : |(151936821/400000000 : ℝ)|=(151936821/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1041560227/5000000000 : ℝ)|^89 ≤ (14770374548753/100000000000000 : ℝ)^73
        have hw : |(1041560227/5000000000 : ℝ)|=(1041560227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s2_s2_7 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1880823173/10000000000 : ℝ)*x 0 + (5298952069/10000000000 : ℝ)*x 1 + (4798841823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1880823173/10000000000 : ℝ)^89 ≤ (6520350628793/50000000000000 : ℝ)^73 := by
    have hnat : (1880823173 : ℕ)^89*50000000000000^73 ≤ 6520350628793^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880823173 10000000000 6520350628793 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5298952069/10000000000 : ℝ)^89 ≤ (46103986817231/100000000000000 : ℝ)^73 := by
    have hnat : (5298952069 : ℕ)^89*100000000000000^73 ≤ 46103986817231^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5298952069 10000000000 46103986817231 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4798841823/10000000000 : ℝ)^89 ≤ (20427655958923/50000000000000 : ℝ)^73 := by
    have hnat : (4798841823 : ℕ)^89*50000000000000^73 ≤ 20427655958923^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4798841823 10000000000 20427655958923 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1880823173/10000000000 : ℝ), (5298952069/10000000000 : ℝ), (4798841823/10000000000 : ℝ)] ![(6520350628793/50000000000000 : ℝ), (46103986817231/100000000000000 : ℝ), (20427655958923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1880823173/10000000000 : ℝ)|^89 ≤ (6520350628793/50000000000000 : ℝ)^73
        have hw : |(-1880823173/10000000000 : ℝ)|=(1880823173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5298952069/10000000000 : ℝ)|^89 ≤ (46103986817231/100000000000000 : ℝ)^73
        have hw : |(5298952069/10000000000 : ℝ)|=(5298952069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4798841823/10000000000 : ℝ)|^89 ≤ (20427655958923/50000000000000 : ℝ)^73
        have hw : |(4798841823/10000000000 : ℝ)|=(4798841823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s2_s2_8 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4669404201/10000000000 : ℝ)*x 0 + (-545263153/5000000000 : ℝ)*x 1 + (6011898611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4669404201/10000000000 : ℝ)^89 ≤ (19757902467703/50000000000000 : ℝ)^73 := by
    have hnat : (4669404201 : ℕ)^89*50000000000000^73 ≤ 19757902467703^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4669404201 10000000000 19757902467703 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545263153/5000000000 : ℝ)^89 ≤ (3354880742529/50000000000000 : ℝ)^73 := by
    have hnat : (545263153 : ℕ)^89*50000000000000^73 ≤ 3354880742529^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545263153 5000000000 3354880742529 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6011898611/10000000000 : ℝ)^89 ≤ (53774433571821/100000000000000 : ℝ)^73 := by
    have hnat : (6011898611 : ℕ)^89*100000000000000^73 ≤ 53774433571821^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6011898611 10000000000 53774433571821 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4669404201/10000000000 : ℝ), (-545263153/5000000000 : ℝ), (6011898611/10000000000 : ℝ)] ![(19757902467703/50000000000000 : ℝ), (3354880742529/50000000000000 : ℝ), (53774433571821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4669404201/10000000000 : ℝ)|^89 ≤ (19757902467703/50000000000000 : ℝ)^73
        have hw : |(4669404201/10000000000 : ℝ)|=(4669404201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-545263153/5000000000 : ℝ)|^89 ≤ (3354880742529/50000000000000 : ℝ)^73
        have hw : |(-545263153/5000000000 : ℝ)|=(545263153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6011898611/10000000000 : ℝ)|^89 ≤ (53774433571821/100000000000000 : ℝ)^73
        have hw : |(6011898611/10000000000 : ℝ)|=(6011898611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s2_s2_9 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (291906631/625000000 : ℝ)*x 0 + (2748356209/5000000000 : ℝ)*x 1 + (-894133741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (291906631/625000000 : ℝ)^89 ≤ (39527174084259/100000000000000 : ℝ)^73 := by
    have hnat : (291906631 : ℕ)^89*100000000000000^73 ≤ 39527174084259^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291906631 625000000 39527174084259 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2748356209/5000000000 : ℝ)^89 ≤ (48210239964367/100000000000000 : ℝ)^73 := by
    have hnat : (2748356209 : ℕ)^89*100000000000000^73 ≤ 48210239964367^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748356209 5000000000 48210239964367 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (894133741/5000000000 : ℝ)^89 ≤ (12262585935109/100000000000000 : ℝ)^73 := by
    have hnat : (894133741 : ℕ)^89*100000000000000^73 ≤ 12262585935109^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894133741 5000000000 12262585935109 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(291906631/625000000 : ℝ), (2748356209/5000000000 : ℝ), (-894133741/5000000000 : ℝ)] ![(39527174084259/100000000000000 : ℝ), (48210239964367/100000000000000 : ℝ), (12262585935109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(291906631/625000000 : ℝ)|^89 ≤ (39527174084259/100000000000000 : ℝ)^73
        have hw : |(291906631/625000000 : ℝ)|=(291906631/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2748356209/5000000000 : ℝ)|^89 ≤ (48210239964367/100000000000000 : ℝ)^73
        have hw : |(2748356209/5000000000 : ℝ)|=(2748356209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-894133741/5000000000 : ℝ)|^89 ≤ (12262585935109/100000000000000 : ℝ)^73
        have hw : |(-894133741/5000000000 : ℝ)|=(894133741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s2_s2_13 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1490155819/2500000000 : ℝ)*x 0 + (2052543281/5000000000 : ℝ)*x 1 + (375464087/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1490155819/2500000000 : ℝ)^89 ≤ (10643158509029/20000000000000 : ℝ)^73 := by
    have hnat : (1490155819 : ℕ)^89*20000000000000^73 ≤ 10643158509029^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1490155819 2500000000 10643158509029 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2052543281/5000000000 : ℝ)^89 ≤ (1055409668807/3125000000000 : ℝ)^73 := by
    have hnat : (2052543281 : ℕ)^89*3125000000000^73 ≤ 1055409668807^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052543281 5000000000 1055409668807 3125000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (375464087/2000000000 : ℝ)^89 ≤ (13011098028143/100000000000000 : ℝ)^73 := by
    have hnat : (375464087 : ℕ)^89*100000000000000^73 ≤ 13011098028143^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375464087 2000000000 13011098028143 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1490155819/2500000000 : ℝ), (2052543281/5000000000 : ℝ), (375464087/2000000000 : ℝ)] ![(10643158509029/20000000000000 : ℝ), (1055409668807/3125000000000 : ℝ), (13011098028143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1490155819/2500000000 : ℝ)|^89 ≤ (10643158509029/20000000000000 : ℝ)^73
        have hw : |(1490155819/2500000000 : ℝ)|=(1490155819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2052543281/5000000000 : ℝ)|^89 ≤ (1055409668807/3125000000000 : ℝ)^73
        have hw : |(2052543281/5000000000 : ℝ)|=(2052543281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(375464087/2000000000 : ℝ)|^89 ≤ (13011098028143/100000000000000 : ℝ)^73
        have hw : |(375464087/2000000000 : ℝ)|=(375464087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s2_s2_14 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-884489971/5000000000 : ℝ)*x 0 + (1342091499/2500000000 : ℝ)*x 1 + (1204568953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (884489971/5000000000 : ℝ)^89 ≤ (605076467463/5000000000000 : ℝ)^73 := by
    have hnat : (884489971 : ℕ)^89*5000000000000^73 ≤ 605076467463^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884489971 5000000000 605076467463 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1342091499/2500000000 : ℝ)^89 ≤ (46841352895167/100000000000000 : ℝ)^73 := by
    have hnat : (1342091499 : ℕ)^89*100000000000000^73 ≤ 46841352895167^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342091499 2500000000 46841352895167 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1204568953/2500000000 : ℝ)^89 ≤ (20528558869927/50000000000000 : ℝ)^73 := by
    have hnat : (1204568953 : ℕ)^89*50000000000000^73 ≤ 20528558869927^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204568953 2500000000 20528558869927 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-884489971/5000000000 : ℝ), (1342091499/2500000000 : ℝ), (1204568953/2500000000 : ℝ)] ![(605076467463/5000000000000 : ℝ), (46841352895167/100000000000000 : ℝ), (20528558869927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-884489971/5000000000 : ℝ)|^89 ≤ (605076467463/5000000000000 : ℝ)^73
        have hw : |(-884489971/5000000000 : ℝ)|=(884489971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1342091499/2500000000 : ℝ)|^89 ≤ (46841352895167/100000000000000 : ℝ)^73
        have hw : |(1342091499/2500000000 : ℝ)|=(1342091499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1204568953/2500000000 : ℝ)|^89 ≤ (20528558869927/50000000000000 : ℝ)^73
        have hw : |(1204568953/2500000000 : ℝ)|=(1204568953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s2_s2_15 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (460595629/1000000000 : ℝ)*x 0 + (-1178041973/10000000000 : ℝ)*x 1 + (6011119879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (460595629/1000000000 : ℝ)^89 ≤ (38862156321899/100000000000000 : ℝ)^73 := by
    have hnat : (460595629 : ℕ)^89*100000000000000^73 ≤ 38862156321899^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460595629 1000000000 38862156321899 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1178041973/10000000000 : ℝ)^89 ≤ (3685951075421/50000000000000 : ℝ)^73 := by
    have hnat : (1178041973 : ℕ)^89*50000000000000^73 ≤ 3685951075421^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178041973 10000000000 3685951075421 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6011119879/10000000000 : ℝ)^89 ≤ (26882970754489/50000000000000 : ℝ)^73 := by
    have hnat : (6011119879 : ℕ)^89*50000000000000^73 ≤ 26882970754489^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6011119879 10000000000 26882970754489 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(460595629/1000000000 : ℝ), (-1178041973/10000000000 : ℝ), (6011119879/10000000000 : ℝ)] ![(38862156321899/100000000000000 : ℝ), (3685951075421/50000000000000 : ℝ), (26882970754489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(460595629/1000000000 : ℝ)|^89 ≤ (38862156321899/100000000000000 : ℝ)^73
        have hw : |(460595629/1000000000 : ℝ)|=(460595629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1178041973/10000000000 : ℝ)|^89 ≤ (3685951075421/50000000000000 : ℝ)^73
        have hw : |(-1178041973/10000000000 : ℝ)|=(1178041973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6011119879/10000000000 : ℝ)|^89 ≤ (26882970754489/50000000000000 : ℝ)^73
        have hw : |(6011119879/10000000000 : ℝ)|=(6011119879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s2_s2_16 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2409110137/5000000000 : ℝ)*x 0 + (5368534777/10000000000 : ℝ)*x 1 + (-1768833843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2409110137/5000000000 : ℝ)^89 ≤ (41056540769319/100000000000000 : ℝ)^73 := by
    have hnat : (2409110137 : ℕ)^89*100000000000000^73 ≤ 41056540769319^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2409110137 5000000000 41056540769319 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5368534777/10000000000 : ℝ)^89 ≤ (9368629674157/20000000000000 : ℝ)^73 := by
    have hnat : (5368534777 : ℕ)^89*20000000000000^73 ≤ 9368629674157^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368534777 10000000000 9368629674157 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1768833843/10000000000 : ℝ)^89 ≤ (3025077710719/25000000000000 : ℝ)^73 := by
    have hnat : (1768833843 : ℕ)^89*25000000000000^73 ≤ 3025077710719^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768833843 10000000000 3025077710719 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2409110137/5000000000 : ℝ), (5368534777/10000000000 : ℝ), (-1768833843/10000000000 : ℝ)] ![(41056540769319/100000000000000 : ℝ), (9368629674157/20000000000000 : ℝ), (3025077710719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2409110137/5000000000 : ℝ)|^89 ≤ (41056540769319/100000000000000 : ℝ)^73
        have hw : |(2409110137/5000000000 : ℝ)|=(2409110137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5368534777/10000000000 : ℝ)|^89 ≤ (9368629674157/20000000000000 : ℝ)^73
        have hw : |(5368534777/10000000000 : ℝ)|=(5368534777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1768833843/10000000000 : ℝ)|^89 ≤ (3025077710719/25000000000000 : ℝ)^73
        have hw : |(-1768833843/10000000000 : ℝ)|=(1768833843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s2_s2_20 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6271026483/10000000000 : ℝ)*x 0 + (3761066959/10000000000 : ℝ)*x 1 + (939876551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6271026483/10000000000 : ℝ)^89 ≤ (2830673047957/5000000000000 : ℝ)^73 := by
    have hnat : (6271026483 : ℕ)^89*5000000000000^73 ≤ 2830673047957^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6271026483 10000000000 2830673047957 5000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3761066959/10000000000 : ℝ)^89 ≤ (30354882708031/100000000000000 : ℝ)^73 := by
    have hnat : (3761066959 : ℕ)^89*100000000000000^73 ≤ 30354882708031^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3761066959 10000000000 30354882708031 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (939876551/5000000000 : ℝ)^89 ≤ (13031656318693/100000000000000 : ℝ)^73 := by
    have hnat : (939876551 : ℕ)^89*100000000000000^73 ≤ 13031656318693^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939876551 5000000000 13031656318693 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6271026483/10000000000 : ℝ), (3761066959/10000000000 : ℝ), (939876551/5000000000 : ℝ)] ![(2830673047957/5000000000000 : ℝ), (30354882708031/100000000000000 : ℝ), (13031656318693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6271026483/10000000000 : ℝ)|^89 ≤ (2830673047957/5000000000000 : ℝ)^73
        have hw : |(6271026483/10000000000 : ℝ)|=(6271026483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3761066959/10000000000 : ℝ)|^89 ≤ (30354882708031/100000000000000 : ℝ)^73
        have hw : |(3761066959/10000000000 : ℝ)|=(3761066959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(939876551/5000000000 : ℝ)|^89 ≤ (13031656318693/100000000000000 : ℝ)^73
        have hw : |(939876551/5000000000 : ℝ)|=(939876551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s2_s2_21 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1792431437/10000000000 : ℝ)*x 0 + (1375530647/2500000000 : ℝ)*x 1 + (4661522097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1792431437/10000000000 : ℝ)^89 ≤ (6148703157261/50000000000000 : ℝ)^73 := by
    have hnat : (1792431437 : ℕ)^89*50000000000000^73 ≤ 6148703157261^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792431437 10000000000 6148703157261 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1375530647/2500000000 : ℝ)^89 ≤ (9653619532889/20000000000000 : ℝ)^73 := by
    have hnat : (1375530647 : ℕ)^89*20000000000000^73 ≤ 9653619532889^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375530647 2500000000 9653619532889 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4661522097/10000000000 : ℝ)^89 ≤ (39434495997571/100000000000000 : ℝ)^73 := by
    have hnat : (4661522097 : ℕ)^89*100000000000000^73 ≤ 39434495997571^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4661522097 10000000000 39434495997571 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1792431437/10000000000 : ℝ), (1375530647/2500000000 : ℝ), (4661522097/10000000000 : ℝ)] ![(6148703157261/50000000000000 : ℝ), (9653619532889/20000000000000 : ℝ), (39434495997571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1792431437/10000000000 : ℝ)|^89 ≤ (6148703157261/50000000000000 : ℝ)^73
        have hw : |(-1792431437/10000000000 : ℝ)|=(1792431437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1375530647/2500000000 : ℝ)|^89 ≤ (9653619532889/20000000000000 : ℝ)^73
        have hw : |(1375530647/2500000000 : ℝ)|=(1375530647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4661522097/10000000000 : ℝ)|^89 ≤ (39434495997571/100000000000000 : ℝ)^73
        have hw : |(4661522097/10000000000 : ℝ)|=(4661522097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s2_s2_22 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4793667499/10000000000 : ℝ)*x 0 + (-1084947553/10000000000 : ℝ)*x 1 + (2948793147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4793667499/10000000000 : ℝ)^89 ≤ (20400805511293/50000000000000 : ℝ)^73 := by
    have hnat : (4793667499 : ℕ)^89*50000000000000^73 ≤ 20400805511293^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4793667499 10000000000 20400805511293 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084947553/10000000000 : ℝ)^89 ≤ (6667936928143/100000000000000 : ℝ)^73 := by
    have hnat : (1084947553 : ℕ)^89*100000000000000^73 ≤ 6667936928143^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084947553 10000000000 6667936928143 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2948793147/5000000000 : ℝ)^89 ≤ (52530452039261/100000000000000 : ℝ)^73 := by
    have hnat : (2948793147 : ℕ)^89*100000000000000^73 ≤ 52530452039261^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2948793147 5000000000 52530452039261 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4793667499/10000000000 : ℝ), (-1084947553/10000000000 : ℝ), (2948793147/5000000000 : ℝ)] ![(20400805511293/50000000000000 : ℝ), (6667936928143/100000000000000 : ℝ), (52530452039261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4793667499/10000000000 : ℝ)|^89 ≤ (20400805511293/50000000000000 : ℝ)^73
        have hw : |(4793667499/10000000000 : ℝ)|=(4793667499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1084947553/10000000000 : ℝ)|^89 ≤ (6667936928143/100000000000000 : ℝ)^73
        have hw : |(-1084947553/10000000000 : ℝ)|=(1084947553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2948793147/5000000000 : ℝ)|^89 ≤ (52530452039261/100000000000000 : ℝ)^73
        have hw : |(2948793147/5000000000 : ℝ)|=(2948793147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s2_s2_23 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1145868023/2500000000 : ℝ)*x 0 + (5502291409/10000000000 : ℝ)*x 1 + (-1887729329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1145868023/2500000000 : ℝ)^89 ≤ (19315496496589/50000000000000 : ℝ)^73 := by
    have hnat : (1145868023 : ℕ)^89*50000000000000^73 ≤ 19315496496589^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145868023 2500000000 19315496496589 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5502291409/10000000000 : ℝ)^89 ≤ (12067475819697/25000000000000 : ℝ)^73 := by
    have hnat : (5502291409 : ℕ)^89*25000000000000^73 ≤ 12067475819697^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502291409 10000000000 12067475819697 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1887729329/10000000000 : ℝ)^89 ≤ (6549551853847/50000000000000 : ℝ)^73 := by
    have hnat : (1887729329 : ℕ)^89*50000000000000^73 ≤ 6549551853847^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887729329 10000000000 6549551853847 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1145868023/2500000000 : ℝ), (5502291409/10000000000 : ℝ), (-1887729329/10000000000 : ℝ)] ![(19315496496589/50000000000000 : ℝ), (12067475819697/25000000000000 : ℝ), (6549551853847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1145868023/2500000000 : ℝ)|^89 ≤ (19315496496589/50000000000000 : ℝ)^73
        have hw : |(1145868023/2500000000 : ℝ)|=(1145868023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5502291409/10000000000 : ℝ)|^89 ≤ (12067475819697/25000000000000 : ℝ)^73
        have hw : |(5502291409/10000000000 : ℝ)|=(5502291409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1887729329/10000000000 : ℝ)|^89 ≤ (6549551853847/50000000000000 : ℝ)^73
        have hw : |(-1887729329/10000000000 : ℝ)|=(1887729329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326055_s2_s2_27 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3172369993/5000000000 : ℝ)*x 0 + (3470118173/10000000000 : ℝ)*x 1 + (529065853/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3172369993/5000000000 : ℝ)^89 ≤ (28712914336659/50000000000000 : ℝ)^73 := by
    have hnat : (3172369993 : ℕ)^89*50000000000000^73 ≤ 28712914336659^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3172369993 5000000000 28712914336659 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3470118173/10000000000 : ℝ)^89 ≤ (6879198018547/25000000000000 : ℝ)^73 := by
    have hnat : (3470118173 : ℕ)^89*25000000000000^73 ≤ 6879198018547^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3470118173 10000000000 6879198018547 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529065853/2500000000 : ℝ)^89 ≤ (7528689621899/50000000000000 : ℝ)^73 := by
    have hnat : (529065853 : ℕ)^89*50000000000000^73 ≤ 7528689621899^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529065853 2500000000 7528689621899 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3172369993/5000000000 : ℝ), (3470118173/10000000000 : ℝ), (529065853/2500000000 : ℝ)] ![(28712914336659/50000000000000 : ℝ), (6879198018547/25000000000000 : ℝ), (7528689621899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3172369993/5000000000 : ℝ)|^89 ≤ (28712914336659/50000000000000 : ℝ)^73
        have hw : |(3172369993/5000000000 : ℝ)|=(3172369993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3470118173/10000000000 : ℝ)|^89 ≤ (6879198018547/25000000000000 : ℝ)^73
        have hw : |(3470118173/10000000000 : ℝ)|=(3470118173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529065853/2500000000 : ℝ)|^89 ≤ (7528689621899/50000000000000 : ℝ)^73
        have hw : |(529065853/2500000000 : ℝ)|=(529065853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326055_s2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((4481/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4481/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18223/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18223/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7153/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7153/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3631/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3631/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19257/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19257/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8959/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8959/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (4481/12500 : ℝ) ^ (87/16 : ℝ) ≤ (188961386162617243/50000000000000000000 : ℝ) := by
    have hpowers : (4481/12500 : ℝ)^87 ≤ (188961386162617243/50000000000000000000 : ℝ)^16 := by
      have hnat : (4481 : ℕ)^87*50000000000000000000^16 ≤ 188961386162617243^16*12500^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4481 12500 188961386162617243 50000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4481/12500 : ℝ)) (X := (188961386162617243/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (50188961386162617243/50000000000000000000 : ℝ) ≤ (1250867451282541/1250000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (50188961386162617243/50000000000000000000 : ℝ)^16 ≤ (1250867451282541/1250000000000000 : ℝ)^87 := by
      have hnat : (50188961386162617243 : ℕ)^16*1250000000000000^87 ≤ 1250867451282541^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50188961386162617243 50000000000000000000 1250867451282541 1250000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250867451282541/1250000000000000 : ℝ)) (X := (50188961386162617243/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (25188961386162617243/25000000000000000000 : ℝ) ≤ (10013857930629351/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (25188961386162617243/25000000000000000000 : ℝ)^16 ≤ (10013857930629351/10000000000000000 : ℝ)^87 := by
      have hnat : (25188961386162617243 : ℕ)^16*10000000000000000^87 ≤ 10013857930629351^87*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25188961386162617243 25000000000000000000 10013857930629351 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013857930629351/10000000000000000 : ℝ)) (X := (25188961386162617243/25000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(867451282541/448100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(6918320369023/3584800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (4481/12500 : ℝ)) (alpha := (867451282541/448100000000000 : ℝ)) (beta := (6918320369023/3584800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (4481/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(867451282541/448100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(6918320369023/3584800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (18223/50000 : ℝ) ^ (87/16 : ℝ) ≤ (51686983333349881/12500000000000000000 : ℝ) := by
    have hpowers : (18223/50000 : ℝ)^87 ≤ (51686983333349881/12500000000000000000 : ℝ)^16 := by
      have hnat : (18223 : ℕ)^87*12500000000000000000^16 ≤ 51686983333349881^16*50000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18223 50000 51686983333349881 12500000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18223/50000 : ℝ)) (X := (51686983333349881/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (12551686983333349881/12500000000000000000 : ℝ) ≤ (2501897930739017/2500000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (12551686983333349881/12500000000000000000 : ℝ)^16 ≤ (2501897930739017/2500000000000000 : ℝ)^87 := by
      have hnat : (12551686983333349881 : ℕ)^16*2500000000000000^87 ≤ 2501897930739017^87*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12551686983333349881 12500000000000000000 2501897930739017 2500000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501897930739017/2500000000000000 : ℝ)) (X := (12551686983333349881/12500000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (6301686983333349881/6250000000000000000 : ℝ) ≤ (400606319032333/400000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (6301686983333349881/6250000000000000000 : ℝ)^16 ≤ (400606319032333/400000000000000 : ℝ)^87 := by
      have hnat : (6301686983333349881 : ℕ)^16*400000000000000^87 ≤ 400606319032333^87*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6301686983333349881 6250000000000000000 400606319032333 400000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400606319032333/400000000000000 : ℝ)) (X := (6301686983333349881/6250000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1897930739017/911150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(7566252852257/3644600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (18223/50000 : ℝ)) (alpha := (1897930739017/911150000000000 : ℝ)) (beta := (7566252852257/3644600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (18223/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1897930739017/911150000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(7566252852257/3644600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (7153/20000 : ℝ) ^ (87/16 : ℝ) ≤ (373189247580383729/100000000000000000000 : ℝ) := by
    have hpowers : (7153/20000 : ℝ)^87 ≤ (373189247580383729/100000000000000000000 : ℝ)^16 := by
      have hnat : (7153 : ℕ)^87*100000000000000000000^16 ≤ 373189247580383729^16*20000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7153 20000 373189247580383729 100000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7153/20000 : ℝ)) (X := (373189247580383729/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (100373189247580383729/100000000000000000000 : ℝ) ≤ (10006852822833209/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (100373189247580383729/100000000000000000000 : ℝ)^16 ≤ (10006852822833209/10000000000000000 : ℝ)^87 := by
      have hnat : (100373189247580383729 : ℕ)^16*10000000000000000^87 ≤ 10006852822833209^87*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100373189247580383729 100000000000000000000 10006852822833209 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006852822833209/10000000000000000 : ℝ)) (X := (100373189247580383729/100000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (50373189247580383729/50000000000000000000 : ℝ) ≤ (625855305248549/625000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (50373189247580383729/50000000000000000000 : ℝ)^16 ≤ (625855305248549/625000000000000 : ℝ)^87 := by
      have hnat : (50373189247580383729 : ℕ)^16*625000000000000^87 ≤ 625855305248549^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50373189247580383729 50000000000000000000 625855305248549 625000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625855305248549/625000000000000 : ℝ)) (X := (50373189247580383729/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(6852822833209/3576500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(273282445743/143060000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (7153/20000 : ℝ)) (alpha := (6852822833209/3576500000000000 : ℝ)) (beta := (273282445743/143060000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (7153/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(6852822833209/3576500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(273282445743/143060000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1918446979/10000000000 : ℝ)*X 0 0+(5396385053/10000000000 : ℝ)*X 0 1+(2333983557/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((233340471/500000000 : ℝ)*X 1 0+(-37182543/312500000 : ℝ)*X 1 1+(1486322531/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((4667911577/10000000000 : ℝ)*X 2 0+(5396554391/10000000000 : ℝ)*X 2 1+(-1918302043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((3039487067/5000000000 : ℝ)*X 0 0+(151936821/400000000 : ℝ)*X 0 1+(1041560227/5000000000 : ℝ)*X 0 2+(3039487067/5000000000 : ℝ)*X 1 0+(151936821/400000000 : ℝ)*X 1 1+(1041560227/5000000000 : ℝ)*X 1 2+(3039487067/5000000000 : ℝ)*X 2 0+(151936821/400000000 : ℝ)*X 2 1+(1041560227/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1880823173/10000000000 : ℝ)*X 0 0+(5298952069/10000000000 : ℝ)*X 0 1+(4798841823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((4669404201/10000000000 : ℝ)*X 1 0+(-545263153/5000000000 : ℝ)*X 1 1+(6011898611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((291906631/625000000 : ℝ)*X 2 0+(2748356209/5000000000 : ℝ)*X 2 1+(-894133741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1490155819/2500000000 : ℝ)*X 0 0+(2052543281/5000000000 : ℝ)*X 0 1+(375464087/2000000000 : ℝ)*X 0 2+(1490155819/2500000000 : ℝ)*X 1 0+(2052543281/5000000000 : ℝ)*X 1 1+(375464087/2000000000 : ℝ)*X 1 2+(1490155819/2500000000 : ℝ)*X 2 0+(2052543281/5000000000 : ℝ)*X 2 1+(375464087/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-884489971/5000000000 : ℝ)*X 0 0+(1342091499/2500000000 : ℝ)*X 0 1+(1204568953/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((460595629/1000000000 : ℝ)*X 1 0+(-1178041973/10000000000 : ℝ)*X 1 1+(6011119879/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((2409110137/5000000000 : ℝ)*X 2 0+(5368534777/10000000000 : ℝ)*X 2 1+(-1768833843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((6271026483/10000000000 : ℝ)*X 0 0+(3761066959/10000000000 : ℝ)*X 0 1+(939876551/5000000000 : ℝ)*X 0 2+(6271026483/10000000000 : ℝ)*X 1 0+(3761066959/10000000000 : ℝ)*X 1 1+(939876551/5000000000 : ℝ)*X 1 2+(6271026483/10000000000 : ℝ)*X 2 0+(3761066959/10000000000 : ℝ)*X 2 1+(939876551/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-1792431437/10000000000 : ℝ)*X 0 0+(1375530647/2500000000 : ℝ)*X 0 1+(4661522097/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((4793667499/10000000000 : ℝ)*X 1 0+(-1084947553/10000000000 : ℝ)*X 1 1+(2948793147/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1145868023/2500000000 : ℝ)*X 2 0+(5502291409/10000000000 : ℝ)*X 2 1+(-1887729329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((3172369993/5000000000 : ℝ)*X 0 0+(3470118173/10000000000 : ℝ)*X 0 1+(529065853/2500000000 : ℝ)*X 0 2+(3172369993/5000000000 : ℝ)*X 1 0+(3470118173/10000000000 : ℝ)*X 1 1+(529065853/2500000000 : ℝ)*X 1 2+(3172369993/5000000000 : ℝ)*X 2 0+(3470118173/10000000000 : ℝ)*X 2 1+(529065853/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326055_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((3631/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3631/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1312134743342055906453806956839/146023600559750000000000000000000000 : ℝ) := by norm_num
    linear_combination (6005462724543/1000000000000 : ℝ)*(base49) + (8350429823569/250000000000 : ℝ)*(major_s2_0) + (8350429823569/250000000000 : ℝ)*(major_s2_1) + (8350429823569/250000000000 : ℝ)*(major_s2_2) + (499440673/1000000000000 : ℝ)*(sp_s2_0) + (15968457/62500000000 : ℝ)*(sp_s2_2) + (18030659/200000000000 : ℝ)*(sp_s2_6) + (10121854608751/200000000000 : ℝ)*(sp_s2_7) + (50609218408931/1000000000000 : ℝ)*(sp_s2_8) + (6326132101473/125000000000 : ℝ)*(sp_s2_9) + (16193505121849/1000000000000 : ℝ)*(sp_s2_13) + (67833719/1000000000000 : ℝ)*(sp_s2_14) + (124381843/200000000000 : ℝ)*(sp_s2_15) + (10560221/20000000000 : ℝ)*(sp_s2_23) + (2024199409393/125000000000 : ℝ)*(f.failure) + (25304920159073/500000000000 : ℝ)*(f.sum) + (1603474741351313249/8146819937500000000000000000000 : ℝ)*base63 + (23563185654319/71530000000000000000000000 : ℝ)*base64 + (696266274493633/911150000000000000000000000 : ℝ)*base66 + (371628686299467/1788250000000000000000000000 : ℝ)*base69 + (2917173421718391/400657412500000000000000000000 : ℝ)*base71 + (181214373340067/896200000000000000000000000 : ℝ)*base73 + (95216861027181/455575000000000000000000000 : ℝ)*base75 + (45764627921023/224050000000000000000000000 : ℝ)*base77 + (8006194970044364551/16331452600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (571/2500000000000000 : ℝ)*base86 + (571/2500000000000000 : ℝ)*base88 + (571/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19257/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19257/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17050729436374880414637/1822300000000000000000000000 : ℝ) := by norm_num
    linear_combination (5523749198449/1000000000000 : ℝ)*(base49) + (409187/200000000000 : ℝ)*(base60) + (31254908663287/1000000000000 : ℝ)*(major_s2_0) + (31254908663287/1000000000000 : ℝ)*(major_s2_1) + (31254908663287/1000000000000 : ℝ)*(major_s2_2) + (25360539/200000000000 : ℝ)*(sp_s2_1) + (76143459/1000000000000 : ℝ)*(sp_s2_2) + (71697537/250000000000 : ℝ)*(sp_s2_7) + (122185969/500000000000 : ℝ)*(sp_s2_8) + (9471346865873/200000000000 : ℝ)*(sp_s2_14) + (591958124311/12500000000 : ℝ)*(sp_s2_15) + (23678472488027/500000000000 : ℝ)*(sp_s2_16) + (7576304172321/500000000000 : ℝ)*(sp_s2_20) + (36948703/200000000000 : ℝ)*(sp_s2_27) + (15152793088157/1000000000000 : ℝ)*(f.failure) + (47357021119513/1000000000000 : ℝ)*(f.sum) + (478242293085129179/65174559500000000000000000000000 : ℝ)*base63 + (13558344793409/143060000000000000000000000 : ℝ)*base64 + (802876407689161/3644600000000000000000000000 : ℝ)*base67 + (461129161834117/3576500000000000000000000000 : ℝ)*base68 + (78637356473646703/1602629650000000000000000000000 : ℝ)*base71 + (499889688948759/3584800000000000000000000000 : ℝ)*base72 + (47601624337673/455575000000000000000000000 : ℝ)*base74 + (50103009089733/448100000000000000000000000 : ℝ)*base76 + (23464353005227548507/65325810400000000000000000000000 : ℝ)*base79 + (721/20000000000000000 : ℝ)*base87 + (721/20000000000000000 : ℝ)*base89 + (721/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8959/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8959/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20228814513961851334446882307677/1168188804478000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106163/250000000000 : ℝ)*(base39) + (1764583/250000000000 : ℝ)*(base40) + (572490422959/100000000000 : ℝ)*(base49) + (31235626198721/1000000000000 : ℝ)*(major_s2_0) + (31235626198721/1000000000000 : ℝ)*(major_s2_1) + (31235626198721/1000000000000 : ℝ)*(major_s2_2) + (766011667/500000000000 : ℝ)*(sp_s2_0) + (1236967879/1000000000000 : ℝ)*(sp_s2_1) + (867447367/1000000000000 : ℝ)*(sp_s2_2) + (168751047/250000000000 : ℝ)*(sp_s2_20) + (23663134953831/500000000000 : ℝ)*(sp_s2_21) + (47326564963117/1000000000000 : ℝ)*(sp_s2_22) + (47326934483629/1000000000000 : ℝ)*(sp_s2_23) + (15142769690123/1000000000000 : ℝ)*(sp_s2_27) + (15143444694311/1000000000000 : ℝ)*(f.failure) + (11831950482749/250000000000 : ℝ)*(f.sum) + (6560278383191051957/65174559500000000000000000000000 : ℝ)*base63 + (19303471676829/143060000000000000000000000 : ℝ)*base65 + (996314387523383/3644600000000000000000000000 : ℝ)*base67 + (619803490491439/3576500000000000000000000000 : ℝ)*base69 + (118665821174673333/801314825000000000000000000000 : ℝ)*base70 + (2345373522753503/3584800000000000000000000000 : ℝ)*base73 + (80884149513361/455575000000000000000000000 : ℝ)*base75 + (31299217822429/448100000000000000000000000 : ℝ)*base76 + (48168055604150590381/65325810400000000000000000000000 : ℝ)*base79 + (8317/20000000000000000 : ℝ)*base86 + (8317/20000000000000000 : ℝ)*base88 + (8317/20000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((4481/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4481/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18223/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18223/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7153/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7153/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3631/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3631/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19257/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19257/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8959/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8959/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c326055_s2 p hpa hpb X hX hprev1

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301060_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:37:31.169163+00:00
-- url     : https://prove2.me/submissions/07e6d5d3-827e-4434-acfa-4bb59ed073b2

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
theorem collision_support_c301060_s5_s5_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2244831999/10000000000 : ℝ)*x 0 + (2113498327/5000000000 : ℝ)*x 1 + (-3155721289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2244831999/10000000000 : ℝ)^65 ≤ (861401304669/6250000000000 : ℝ)^49 := by
    have hnat : (2244831999 : ℕ)^65*6250000000000^49 ≤ 861401304669^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244831999 10000000000 861401304669 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113498327/5000000000 : ℝ)^65 ≤ (31909490710697/100000000000000 : ℝ)^49 := by
    have hnat : (2113498327 : ℕ)^65*100000000000000^49 ≤ 31909490710697^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113498327 5000000000 31909490710697 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3155721289/5000000000 : ℝ)^65 ≤ (54308088399009/100000000000000 : ℝ)^49 := by
    have hnat : (3155721289 : ℕ)^65*100000000000000^49 ≤ 54308088399009^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3155721289 5000000000 54308088399009 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2244831999/10000000000 : ℝ), (2113498327/5000000000 : ℝ), (-3155721289/5000000000 : ℝ)] ![(861401304669/6250000000000 : ℝ), (31909490710697/100000000000000 : ℝ), (54308088399009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2244831999/10000000000 : ℝ)|^65 ≤ (861401304669/6250000000000 : ℝ)^49
        have hw : |(-2244831999/10000000000 : ℝ)|=(2244831999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113498327/5000000000 : ℝ)|^65 ≤ (31909490710697/100000000000000 : ℝ)^49
        have hw : |(2113498327/5000000000 : ℝ)|=(2113498327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3155721289/5000000000 : ℝ)|^65 ≤ (54308088399009/100000000000000 : ℝ)^49
        have hw : |(-3155721289/5000000000 : ℝ)|=(3155721289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301060_s5_s5_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4475956923/10000000000 : ℝ)*x 0 + (-2530739921/10000000000 : ℝ)*x 1 + (-5877887331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4475956923/10000000000 : ℝ)^65 ≤ (34426229274941/100000000000000 : ℝ)^49 := by
    have hnat : (4475956923 : ℕ)^65*100000000000000^49 ≤ 34426229274941^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475956923 10000000000 34426229274941 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2530739921/10000000000 : ℝ)^65 ≤ (16158072851593/100000000000000 : ℝ)^49 := by
    have hnat : (2530739921 : ℕ)^65*100000000000000^49 ≤ 16158072851593^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2530739921 10000000000 16158072851593 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5877887331/10000000000 : ℝ)^65 ≤ (24707848929163/50000000000000 : ℝ)^49 := by
    have hnat : (5877887331 : ℕ)^65*50000000000000^49 ≤ 24707848929163^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5877887331 10000000000 24707848929163 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4475956923/10000000000 : ℝ), (-2530739921/10000000000 : ℝ), (-5877887331/10000000000 : ℝ)] ![(34426229274941/100000000000000 : ℝ), (16158072851593/100000000000000 : ℝ), (24707848929163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4475956923/10000000000 : ℝ)|^65 ≤ (34426229274941/100000000000000 : ℝ)^49
        have hw : |(4475956923/10000000000 : ℝ)|=(4475956923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2530739921/10000000000 : ℝ)|^65 ≤ (16158072851593/100000000000000 : ℝ)^49
        have hw : |(-2530739921/10000000000 : ℝ)|=(2530739921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5877887331/10000000000 : ℝ)|^65 ≤ (24707848929163/50000000000000 : ℝ)^49
        have hw : |(-5877887331/10000000000 : ℝ)|=(5877887331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301060_s5_s5_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4745951513/10000000000 : ℝ)*x 0 + (5888401979/10000000000 : ℝ)*x 1 + (436059171/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4745951513/10000000000 : ℝ)^65 ≤ (37207710284907/100000000000000 : ℝ)^49 := by
    have hnat : (4745951513 : ℕ)^65*100000000000000^49 ≤ 37207710284907^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4745951513 10000000000 37207710284907 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5888401979/10000000000 : ℝ)^65 ≤ (49532993657889/100000000000000 : ℝ)^49 := by
    have hnat : (5888401979 : ℕ)^65*100000000000000^49 ≤ 49532993657889^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5888401979 10000000000 49532993657889 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436059171/2000000000 : ℝ)^65 ≤ (6629648020463/50000000000000 : ℝ)^49 := by
    have hnat : (436059171 : ℕ)^65*50000000000000^49 ≤ 6629648020463^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436059171 2000000000 6629648020463 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4745951513/10000000000 : ℝ), (5888401979/10000000000 : ℝ), (436059171/2000000000 : ℝ)] ![(37207710284907/100000000000000 : ℝ), (49532993657889/100000000000000 : ℝ), (6629648020463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4745951513/10000000000 : ℝ)|^65 ≤ (37207710284907/100000000000000 : ℝ)^49
        have hw : |(4745951513/10000000000 : ℝ)|=(4745951513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5888401979/10000000000 : ℝ)|^65 ≤ (49532993657889/100000000000000 : ℝ)^49
        have hw : |(5888401979/10000000000 : ℝ)|=(5888401979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(436059171/2000000000 : ℝ)|^65 ≤ (6629648020463/50000000000000 : ℝ)^49
        have hw : |(436059171/2000000000 : ℝ)|=(436059171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301060_s5_s5_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6829206823/10000000000 : ℝ)*x 0 + (179548279/400000000 : ℝ)*x 1 + (-534234867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6829206823/10000000000 : ℝ)^65 ≤ (60295803504533/100000000000000 : ℝ)^49 := by
    have hnat : (6829206823 : ℕ)^65*100000000000000^49 ≤ 60295803504533^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6829206823 10000000000 60295803504533 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179548279/400000000 : ℝ)^65 ≤ (17278188202157/50000000000000 : ℝ)^49 := by
    have hnat : (179548279 : ℕ)^65*50000000000000^49 ≤ 17278188202157^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179548279 400000000 17278188202157 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (534234867/5000000000 : ℝ)^65 ≤ (64347750943/1250000000000 : ℝ)^49 := by
    have hnat : (534234867 : ℕ)^65*1250000000000^49 ≤ 64347750943^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534234867 5000000000 64347750943 1250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6829206823/10000000000 : ℝ), (179548279/400000000 : ℝ), (-534234867/5000000000 : ℝ)] ![(60295803504533/100000000000000 : ℝ), (17278188202157/50000000000000 : ℝ), (64347750943/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6829206823/10000000000 : ℝ)|^65 ≤ (60295803504533/100000000000000 : ℝ)^49
        have hw : |(6829206823/10000000000 : ℝ)|=(6829206823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179548279/400000000 : ℝ)|^65 ≤ (17278188202157/50000000000000 : ℝ)^49
        have hw : |(179548279/400000000 : ℝ)|=(179548279/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-534234867/5000000000 : ℝ)|^65 ≤ (64347750943/1250000000000 : ℝ)^49
        have hw : |(-534234867/5000000000 : ℝ)|=(534234867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301060_s5_s5_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-390341809/2000000000 : ℝ)*x 0 + (3801208227/10000000000 : ℝ)*x 1 + (-3437595631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390341809/2000000000 : ℝ)^65 ≤ (2861896235843/25000000000000 : ℝ)^49 := by
    have hnat : (390341809 : ℕ)^65*25000000000000^49 ≤ 2861896235843^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390341809 2000000000 2861896235843 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3801208227/10000000000 : ℝ)^65 ≤ (554348936687/2000000000000 : ℝ)^49 := by
    have hnat : (3801208227 : ℕ)^65*2000000000000^49 ≤ 554348936687^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3801208227 10000000000 554348936687 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3437595631/5000000000 : ℝ)^65 ≤ (60834968203309/100000000000000 : ℝ)^49 := by
    have hnat : (3437595631 : ℕ)^65*100000000000000^49 ≤ 60834968203309^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3437595631 5000000000 60834968203309 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-390341809/2000000000 : ℝ), (3801208227/10000000000 : ℝ), (-3437595631/5000000000 : ℝ)] ![(2861896235843/25000000000000 : ℝ), (554348936687/2000000000000 : ℝ), (60834968203309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-390341809/2000000000 : ℝ)|^65 ≤ (2861896235843/25000000000000 : ℝ)^49
        have hw : |(-390341809/2000000000 : ℝ)|=(390341809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3801208227/10000000000 : ℝ)|^65 ≤ (554348936687/2000000000000 : ℝ)^49
        have hw : |(3801208227/10000000000 : ℝ)|=(3801208227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3437595631/5000000000 : ℝ)|^65 ≤ (60834968203309/100000000000000 : ℝ)^49
        have hw : |(-3437595631/5000000000 : ℝ)|=(3437595631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301060_s5_s5_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4060592849/10000000000 : ℝ)*x 0 + (-1577015597/10000000000 : ℝ)*x 1 + (-6899304509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4060592849/10000000000 : ℝ)^65 ≤ (30253938341051/100000000000000 : ℝ)^49 := by
    have hnat : (4060592849 : ℕ)^65*100000000000000^49 ≤ 30253938341051^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4060592849 10000000000 30253938341051 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1577015597/10000000000 : ℝ)^65 ≤ (8627895629289/100000000000000 : ℝ)^49 := by
    have hnat : (1577015597 : ℕ)^65*100000000000000^49 ≤ 8627895629289^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577015597 10000000000 8627895629289 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6899304509/10000000000 : ℝ)^65 ≤ (61118166013311/100000000000000 : ℝ)^49 := by
    have hnat : (6899304509 : ℕ)^65*100000000000000^49 ≤ 61118166013311^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6899304509 10000000000 61118166013311 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4060592849/10000000000 : ℝ), (-1577015597/10000000000 : ℝ), (-6899304509/10000000000 : ℝ)] ![(30253938341051/100000000000000 : ℝ), (8627895629289/100000000000000 : ℝ), (61118166013311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4060592849/10000000000 : ℝ)|^65 ≤ (30253938341051/100000000000000 : ℝ)^49
        have hw : |(4060592849/10000000000 : ℝ)|=(4060592849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1577015597/10000000000 : ℝ)|^65 ≤ (8627895629289/100000000000000 : ℝ)^49
        have hw : |(-1577015597/10000000000 : ℝ)|=(1577015597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6899304509/10000000000 : ℝ)|^65 ≤ (61118166013311/100000000000000 : ℝ)^49
        have hw : |(-6899304509/10000000000 : ℝ)|=(6899304509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301060_s5_s5_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (270885789/625000000 : ℝ)*x 0 + (3426163003/5000000000 : ℝ)*x 1 + (1265883307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270885789/625000000 : ℝ)^65 ≤ (32987162917757/100000000000000 : ℝ)^49 := by
    have hnat : (270885789 : ℕ)^65*100000000000000^49 ≤ 32987162917757^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270885789 625000000 32987162917757 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3426163003/5000000000 : ℝ)^65 ≤ (15141681703257/25000000000000 : ℝ)^49 := by
    have hnat : (3426163003 : ℕ)^65*25000000000000^49 ≤ 15141681703257^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3426163003 5000000000 15141681703257 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1265883307/10000000000 : ℝ)^65 ≤ (6446110254059/100000000000000 : ℝ)^49 := by
    have hnat : (1265883307 : ℕ)^65*100000000000000^49 ≤ 6446110254059^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265883307 10000000000 6446110254059 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270885789/625000000 : ℝ), (3426163003/5000000000 : ℝ), (1265883307/10000000000 : ℝ)] ![(32987162917757/100000000000000 : ℝ), (15141681703257/25000000000000 : ℝ), (6446110254059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270885789/625000000 : ℝ)|^65 ≤ (32987162917757/100000000000000 : ℝ)^49
        have hw : |(270885789/625000000 : ℝ)|=(270885789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3426163003/5000000000 : ℝ)|^65 ≤ (15141681703257/25000000000000 : ℝ)^49
        have hw : |(3426163003/5000000000 : ℝ)|=(3426163003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1265883307/10000000000 : ℝ)|^65 ≤ (6446110254059/100000000000000 : ℝ)^49
        have hw : |(1265883307/10000000000 : ℝ)|=(1265883307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301060_s5_s5_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1549187697/2500000000 : ℝ)*x 0 + (5631512933/10000000000 : ℝ)*x 1 + (-25703697/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1549187697/2500000000 : ℝ)^65 ≤ (53002850221521/100000000000000 : ℝ)^49 := by
    have hnat : (1549187697 : ℕ)^65*100000000000000^49 ≤ 53002850221521^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1549187697 2500000000 53002850221521 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5631512933/10000000000 : ℝ)^65 ≤ (2334353087241/5000000000000 : ℝ)^49 := by
    have hnat : (5631512933 : ℕ)^65*5000000000000^49 ≤ 2334353087241^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5631512933 10000000000 2334353087241 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25703697/2000000000 : ℝ)^65 ≤ (15504400577/5000000000000 : ℝ)^49 := by
    have hnat : (25703697 : ℕ)^65*5000000000000^49 ≤ 15504400577^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25703697 2000000000 15504400577 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1549187697/2500000000 : ℝ), (5631512933/10000000000 : ℝ), (-25703697/2000000000 : ℝ)] ![(53002850221521/100000000000000 : ℝ), (2334353087241/5000000000000 : ℝ), (15504400577/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1549187697/2500000000 : ℝ)|^65 ≤ (53002850221521/100000000000000 : ℝ)^49
        have hw : |(1549187697/2500000000 : ℝ)|=(1549187697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5631512933/10000000000 : ℝ)|^65 ≤ (2334353087241/5000000000000 : ℝ)^49
        have hw : |(5631512933/10000000000 : ℝ)|=(5631512933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25703697/2000000000 : ℝ)|^65 ≤ (15504400577/5000000000000 : ℝ)^49
        have hw : |(-25703697/2000000000 : ℝ)|=(25703697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301060_s5_s5_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1265585813/10000000000 : ℝ)*x 0 + (4324763511/10000000000 : ℝ)*x 1 + (-857574359/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1265585813/10000000000 : ℝ)^65 ≤ (32220503889/500000000000 : ℝ)^49 := by
    have hnat : (1265585813 : ℕ)^65*500000000000^49 ≤ 32220503889^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265585813 10000000000 32220503889 500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4324763511/10000000000 : ℝ)^65 ≤ (16446100367329/50000000000000 : ℝ)^49 := by
    have hnat : (4324763511 : ℕ)^65*50000000000000^49 ≤ 16446100367329^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324763511 10000000000 16446100367329 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (857574359/1250000000 : ℝ)^65 ≤ (60663698477303/100000000000000 : ℝ)^49 := by
    have hnat : (857574359 : ℕ)^65*100000000000000^49 ≤ 60663698477303^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857574359 1250000000 60663698477303 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1265585813/10000000000 : ℝ), (4324763511/10000000000 : ℝ), (-857574359/1250000000 : ℝ)] ![(32220503889/500000000000 : ℝ), (16446100367329/50000000000000 : ℝ), (60663698477303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1265585813/10000000000 : ℝ)|^65 ≤ (32220503889/500000000000 : ℝ)^49
        have hw : |(-1265585813/10000000000 : ℝ)|=(1265585813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4324763511/10000000000 : ℝ)|^65 ≤ (16446100367329/50000000000000 : ℝ)^49
        have hw : |(4324763511/10000000000 : ℝ)|=(4324763511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-857574359/1250000000 : ℝ)|^65 ≤ (60663698477303/100000000000000 : ℝ)^49
        have hw : |(-857574359/1250000000 : ℝ)|=(857574359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301060_s5_s5_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1007592113/2500000000 : ℝ)*x 0 + (-328265909/2000000000 : ℝ)*x 1 + (-688470701/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1007592113/2500000000 : ℝ)^65 ≤ (29955579841123/100000000000000 : ℝ)^49 := by
    have hnat : (1007592113 : ℕ)^65*100000000000000^49 ≤ 29955579841123^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007592113 2500000000 29955579841123 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328265909/2000000000 : ℝ)^65 ≤ (9097733000367/100000000000000 : ℝ)^49 := by
    have hnat : (328265909 : ℕ)^65*100000000000000^49 ≤ 9097733000367^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328265909 2000000000 9097733000367 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (688470701/1000000000 : ℝ)^65 ≤ (60946687143263/100000000000000 : ℝ)^49 := by
    have hnat : (688470701 : ℕ)^65*100000000000000^49 ≤ 60946687143263^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688470701 1000000000 60946687143263 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1007592113/2500000000 : ℝ), (-328265909/2000000000 : ℝ), (-688470701/1000000000 : ℝ)] ![(29955579841123/100000000000000 : ℝ), (9097733000367/100000000000000 : ℝ), (60946687143263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1007592113/2500000000 : ℝ)|^65 ≤ (29955579841123/100000000000000 : ℝ)^49
        have hw : |(1007592113/2500000000 : ℝ)|=(1007592113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-328265909/2000000000 : ℝ)|^65 ≤ (9097733000367/100000000000000 : ℝ)^49
        have hw : |(-328265909/2000000000 : ℝ)|=(328265909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-688470701/1000000000 : ℝ)|^65 ≤ (60946687143263/100000000000000 : ℝ)^49
        have hw : |(-688470701/1000000000 : ℝ)|=(688470701/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301060_s5_s5_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (290901427/500000000 : ℝ)*x 0 + (272520059/500000000 : ℝ)*x 1 + (640240627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (290901427/500000000 : ℝ)^65 ≤ (12187313123107/25000000000000 : ℝ)^49 := by
    have hnat : (290901427 : ℕ)^65*25000000000000^49 ≤ 12187313123107^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290901427 500000000 12187313123107 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272520059/500000000 : ℝ)^65 ≤ (8941168770269/20000000000000 : ℝ)^49 := by
    have hnat : (272520059 : ℕ)^65*20000000000000^49 ≤ 8941168770269^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272520059 500000000 8941168770269 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (640240627/5000000000 : ℝ)^65 ≤ (3272451824629/50000000000000 : ℝ)^49 := by
    have hnat : (640240627 : ℕ)^65*50000000000000^49 ≤ 3272451824629^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640240627 5000000000 3272451824629 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(290901427/500000000 : ℝ), (272520059/500000000 : ℝ), (640240627/5000000000 : ℝ)] ![(12187313123107/25000000000000 : ℝ), (8941168770269/20000000000000 : ℝ), (3272451824629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(290901427/500000000 : ℝ)|^65 ≤ (12187313123107/25000000000000 : ℝ)^49
        have hw : |(290901427/500000000 : ℝ)|=(290901427/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272520059/500000000 : ℝ)|^65 ≤ (8941168770269/20000000000000 : ℝ)^49
        have hw : |(272520059/500000000 : ℝ)|=(272520059/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(640240627/5000000000 : ℝ)|^65 ≤ (3272451824629/50000000000000 : ℝ)^49
        have hw : |(640240627/5000000000 : ℝ)|=(640240627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301060_s5_s5_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (977285791/1250000000 : ℝ)*x 0 + (1886749397/5000000000 : ℝ)*x 1 + (-31421527/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977285791/1250000000 : ℝ)^65 ≤ (3607274832883/5000000000000 : ℝ)^49 := by
    have hnat : (977285791 : ℕ)^65*5000000000000^49 ≤ 3607274832883^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977285791 1250000000 3607274832883 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1886749397/5000000000 : ℝ)^65 ≤ (27449740623063/100000000000000 : ℝ)^49 := by
    have hnat : (1886749397 : ℕ)^65*100000000000000^49 ≤ 27449740623063^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886749397 5000000000 27449740623063 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31421527/2000000000 : ℝ)^65 ≤ (101190675913/25000000000000 : ℝ)^49 := by
    have hnat : (31421527 : ℕ)^65*25000000000000^49 ≤ 101190675913^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31421527 2000000000 101190675913 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(977285791/1250000000 : ℝ), (1886749397/5000000000 : ℝ), (-31421527/2000000000 : ℝ)] ![(3607274832883/5000000000000 : ℝ), (27449740623063/100000000000000 : ℝ), (101190675913/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(977285791/1250000000 : ℝ)|^65 ≤ (3607274832883/5000000000000 : ℝ)^49
        have hw : |(977285791/1250000000 : ℝ)|=(977285791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1886749397/5000000000 : ℝ)|^65 ≤ (27449740623063/100000000000000 : ℝ)^49
        have hw : |(1886749397/5000000000 : ℝ)|=(1886749397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31421527/2000000000 : ℝ)|^65 ≤ (101190675913/25000000000000 : ℝ)^49
        have hw : |(-31421527/2000000000 : ℝ)|=(31421527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301060_s5_s5_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-98131643/1000000000 : ℝ)*x 0 + (2726096041/5000000000 : ℝ)*x 1 + (-599057217/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98131643/1000000000 : ℝ)^65 ≤ (4598369529383/100000000000000 : ℝ)^49 := by
    have hnat : (98131643 : ℕ)^65*100000000000000^49 ≤ 4598369529383^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98131643 1000000000 4598369529383 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726096041/5000000000 : ℝ)^65 ≤ (44725330996531/100000000000000 : ℝ)^49 := by
    have hnat : (2726096041 : ℕ)^65*100000000000000^49 ≤ 44725330996531^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726096041 5000000000 44725330996531 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (599057217/1000000000 : ℝ)^65 ≤ (50676299460613/100000000000000 : ℝ)^49 := by
    have hnat : (599057217 : ℕ)^65*100000000000000^49 ≤ 50676299460613^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599057217 1000000000 50676299460613 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98131643/1000000000 : ℝ), (2726096041/5000000000 : ℝ), (-599057217/1000000000 : ℝ)] ![(4598369529383/100000000000000 : ℝ), (44725330996531/100000000000000 : ℝ), (50676299460613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98131643/1000000000 : ℝ)|^65 ≤ (4598369529383/100000000000000 : ℝ)^49
        have hw : |(-98131643/1000000000 : ℝ)|=(98131643/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726096041/5000000000 : ℝ)|^65 ≤ (44725330996531/100000000000000 : ℝ)^49
        have hw : |(2726096041/5000000000 : ℝ)|=(2726096041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-599057217/1000000000 : ℝ)|^65 ≤ (50676299460613/100000000000000 : ℝ)^49
        have hw : |(-599057217/1000000000 : ℝ)|=(599057217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301060_s5_s5_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5828718407/10000000000 : ℝ)*x 0 + (-279055887/2000000000 : ℝ)*x 1 + (-2683351831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5828718407/10000000000 : ℝ)^65 ≤ (48868105971193/100000000000000 : ℝ)^49 := by
    have hnat : (5828718407 : ℕ)^65*100000000000000^49 ≤ 48868105971193^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5828718407 10000000000 48868105971193 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279055887/2000000000 : ℝ)^65 ≤ (45840242487/625000000000 : ℝ)^49 := by
    have hnat : (279055887 : ℕ)^65*625000000000^49 ≤ 45840242487^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279055887 2000000000 45840242487 625000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2683351831/5000000000 : ℝ)^65 ≤ (43797455214907/100000000000000 : ℝ)^49 := by
    have hnat : (2683351831 : ℕ)^65*100000000000000^49 ≤ 43797455214907^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683351831 5000000000 43797455214907 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5828718407/10000000000 : ℝ), (-279055887/2000000000 : ℝ), (-2683351831/5000000000 : ℝ)] ![(48868105971193/100000000000000 : ℝ), (45840242487/625000000000 : ℝ), (43797455214907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5828718407/10000000000 : ℝ)|^65 ≤ (48868105971193/100000000000000 : ℝ)^49
        have hw : |(5828718407/10000000000 : ℝ)|=(5828718407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-279055887/2000000000 : ℝ)|^65 ≤ (45840242487/625000000000 : ℝ)^49
        have hw : |(-279055887/2000000000 : ℝ)|=(279055887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2683351831/5000000000 : ℝ)|^65 ≤ (43797455214907/100000000000000 : ℝ)^49
        have hw : |(-2683351831/5000000000 : ℝ)|=(2683351831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301060_s5_s5_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (258210741/625000000 : ℝ)*x 0 + (205557143/312500000 : ℝ)*x 1 + (99043661/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258210741/625000000 : ℝ)^65 ≤ (15477732031363/50000000000000 : ℝ)^49 := by
    have hnat : (258210741 : ℕ)^65*50000000000000^49 ≤ 15477732031363^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258210741 625000000 15477732031363 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205557143/312500000 : ℝ)^65 ≤ (28684741441869/50000000000000 : ℝ)^49 := by
    have hnat : (205557143 : ℕ)^65*50000000000000^49 ≤ 28684741441869^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205557143 312500000 28684741441869 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99043661/500000000 : ℝ)^65 ≤ (5837526518311/50000000000000 : ℝ)^49 := by
    have hnat : (99043661 : ℕ)^65*50000000000000^49 ≤ 5837526518311^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99043661 500000000 5837526518311 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258210741/625000000 : ℝ), (205557143/312500000 : ℝ), (99043661/500000000 : ℝ)] ![(15477732031363/50000000000000 : ℝ), (28684741441869/50000000000000 : ℝ), (5837526518311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258210741/625000000 : ℝ)|^65 ≤ (15477732031363/50000000000000 : ℝ)^49
        have hw : |(258210741/625000000 : ℝ)|=(258210741/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205557143/312500000 : ℝ)|^65 ≤ (28684741441869/50000000000000 : ℝ)^49
        have hw : |(205557143/312500000 : ℝ)|=(205557143/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(99043661/500000000 : ℝ)|^65 ≤ (5837526518311/50000000000000 : ℝ)^49
        have hw : |(99043661/500000000 : ℝ)|=(99043661/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301060_s5_s5_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1631255549/2000000000 : ℝ)*x 0 + (3291614299/10000000000 : ℝ)*x 1 + (-51951277/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1631255549/2000000000 : ℝ)^65 ≤ (19077938553247/25000000000000 : ℝ)^49 := by
    have hnat : (1631255549 : ℕ)^65*25000000000000^49 ≤ 19077938553247^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1631255549 2000000000 19077938553247 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3291614299/10000000000 : ℝ)^65 ≤ (11449807638151/50000000000000 : ℝ)^49 := by
    have hnat : (3291614299 : ℕ)^65*50000000000000^49 ≤ 11449807638151^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3291614299 10000000000 11449807638151 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51951277/2000000000 : ℝ)^65 ≤ (12322351657/1562500000000 : ℝ)^49 := by
    have hnat : (51951277 : ℕ)^65*1562500000000^49 ≤ 12322351657^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51951277 2000000000 12322351657 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1631255549/2000000000 : ℝ), (3291614299/10000000000 : ℝ), (-51951277/2000000000 : ℝ)] ![(19077938553247/25000000000000 : ℝ), (11449807638151/50000000000000 : ℝ), (12322351657/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1631255549/2000000000 : ℝ)|^65 ≤ (19077938553247/25000000000000 : ℝ)^49
        have hw : |(1631255549/2000000000 : ℝ)|=(1631255549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3291614299/10000000000 : ℝ)|^65 ≤ (11449807638151/50000000000000 : ℝ)^49
        have hw : |(3291614299/10000000000 : ℝ)|=(3291614299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51951277/2000000000 : ℝ)|^65 ≤ (12322351657/1562500000000 : ℝ)^49
        have hw : |(-51951277/2000000000 : ℝ)|=(51951277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301060_s5 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev4 : (0 : ℝ) ≤ ((75023/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75023/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76509/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76509/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64621/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-64621/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6787/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6787/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58213/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(58213/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10371/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10371/25000 : ℝ)*X 1 2) := by
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
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (75023/100000 : ℝ) ^ (129/32 : ℝ) ≤ (31396232194142675677/100000000000000000000 : ℝ) := by
    have hpowers : (75023/100000 : ℝ)^129 ≤ (31396232194142675677/100000000000000000000 : ℝ)^32 := by
      have hnat : (75023 : ℕ)^129*100000000000000000000^32 ≤ 31396232194142675677^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75023 100000 31396232194142675677 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75023/100000 : ℝ)) (X := (31396232194142675677/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner0a : (131396232194142675677/100000000000000000000 : ℝ) ≤ (2140158369134879/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (131396232194142675677/100000000000000000000 : ℝ)^32 ≤ (2140158369134879/2000000000000000 : ℝ)^129 := by
      have hnat : (131396232194142675677 : ℕ)^32*2000000000000000^129 ≤ 2140158369134879^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        131396232194142675677 100000000000000000000 2140158369134879 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2140158369134879/2000000000000000 : ℝ)) (X := (131396232194142675677/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner0b : (81396232194142675677/50000000000000000000 : ℝ) ≤ (2821229647672931/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (81396232194142675677/50000000000000000000 : ℝ)^32 ≤ (2821229647672931/2500000000000000 : ℝ)^129 := by
      have hnat : (81396232194142675677 : ℕ)^32*2500000000000000^129 ≤ 2821229647672931^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81396232194142675677 50000000000000000000 2821229647672931 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2821229647672931/2500000000000000 : ℝ)) (X := (81396232194142675677/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(140158369134879/1500460000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(584126745017329/7502300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (75023/100000 : ℝ)) (alpha := (140158369134879/1500460000000000 : ℝ)) (beta := (584126745017329/7502300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (75023/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(140158369134879/1500460000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(584126745017329/7502300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (76509/100000 : ℝ) ^ (129/32 : ℝ) ≤ (16989716155044241839/50000000000000000000 : ℝ) := by
    have hpowers : (76509/100000 : ℝ)^129 ≤ (16989716155044241839/50000000000000000000 : ℝ)^32 := by
      have hnat : (76509 : ℕ)^129*50000000000000000000^32 ≤ 16989716155044241839^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76509 100000 16989716155044241839 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (76509/100000 : ℝ)) (X := (16989716155044241839/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner1a : (66989716155044241839/50000000000000000000 : ℝ) ≤ (10752596166684103/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (66989716155044241839/50000000000000000000 : ℝ)^32 ≤ (10752596166684103/10000000000000000 : ℝ)^129 := by
      have hnat : (66989716155044241839 : ℕ)^32*10000000000000000^129 ≤ 10752596166684103^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66989716155044241839 50000000000000000000 10752596166684103 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10752596166684103/10000000000000000 : ℝ)) (X := (66989716155044241839/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner1b : (41989716155044241839/25000000000000000000 : ℝ) ≤ (2274543716946031/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (41989716155044241839/25000000000000000000 : ℝ)^32 ≤ (2274543716946031/2000000000000000 : ℝ)^129 := by
      have hnat : (41989716155044241839 : ℕ)^32*2000000000000000^129 ≤ 2274543716946031^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41989716155044241839 25000000000000000000 2274543716946031 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2274543716946031/2000000000000000 : ℝ)) (X := (41989716155044241839/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(250865388894701/2550300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(155030604511513/1912725000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (76509/100000 : ℝ)) (alpha := (250865388894701/2550300000000000 : ℝ)) (beta := (155030604511513/1912725000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (76509/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(250865388894701/2550300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(155030604511513/1912725000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (64621/100000 : ℝ) ^ (129/32 : ℝ) ≤ (4300400300067879727/25000000000000000000 : ℝ) := by
    have hpowers : (64621/100000 : ℝ)^129 ≤ (4300400300067879727/25000000000000000000 : ℝ)^32 := by
      have hnat : (64621 : ℕ)^129*25000000000000000000^32 ≤ 4300400300067879727^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64621 100000 4300400300067879727 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64621/100000 : ℝ)) (X := (4300400300067879727/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner2a : (29300400300067879727/25000000000000000000 : ℝ) ≤ (208031830151789/200000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (29300400300067879727/25000000000000000000 : ℝ)^32 ≤ (208031830151789/200000000000000 : ℝ)^129 := by
      have hnat : (29300400300067879727 : ℕ)^32*200000000000000^129 ≤ 208031830151789^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29300400300067879727 25000000000000000000 208031830151789 200000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (208031830151789/200000000000000 : ℝ)) (X := (29300400300067879727/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s5_corner2b : (16800400300067879727/12500000000000000000 : ℝ) ≤ (5380511359938539/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (16800400300067879727/12500000000000000000 : ℝ)^32 ≤ (5380511359938539/5000000000000000 : ℝ)^129 := by
      have hnat : (16800400300067879727 : ℕ)^32*5000000000000000^129 ≤ 5380511359938539^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16800400300067879727 12500000000000000000 5380511359938539 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5380511359938539/5000000000000000 : ℝ)) (X := (16800400300067879727/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(8031830151789/129242000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(89857803071907/1615525000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (64621/100000 : ℝ)) (alpha := (8031830151789/129242000000000 : ℝ)) (beta := (89857803071907/1615525000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (64621/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(8031830151789/129242000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(89857803071907/1615525000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-2244831999/10000000000 : ℝ)*X 0 0+(2113498327/5000000000 : ℝ)*X 0 1+(-3155721289/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((4475956923/10000000000 : ℝ)*X 1 0+(-2530739921/10000000000 : ℝ)*X 1 1+(-5877887331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((4745951513/10000000000 : ℝ)*X 2 0+(5888401979/10000000000 : ℝ)*X 2 1+(436059171/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((6829206823/10000000000 : ℝ)*X 0 0+(179548279/400000000 : ℝ)*X 0 1+(-534234867/5000000000 : ℝ)*X 0 2+(6829206823/10000000000 : ℝ)*X 1 0+(179548279/400000000 : ℝ)*X 1 1+(-534234867/5000000000 : ℝ)*X 1 2+(6829206823/10000000000 : ℝ)*X 2 0+(179548279/400000000 : ℝ)*X 2 1+(-534234867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-390341809/2000000000 : ℝ)*X 0 0+(3801208227/10000000000 : ℝ)*X 0 1+(-3437595631/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((4060592849/10000000000 : ℝ)*X 1 0+(-1577015597/10000000000 : ℝ)*X 1 1+(-6899304509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((270885789/625000000 : ℝ)*X 2 0+(3426163003/5000000000 : ℝ)*X 2 1+(1265883307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((1549187697/2500000000 : ℝ)*X 0 0+(5631512933/10000000000 : ℝ)*X 0 1+(-25703697/2000000000 : ℝ)*X 0 2+(1549187697/2500000000 : ℝ)*X 1 0+(5631512933/10000000000 : ℝ)*X 1 1+(-25703697/2000000000 : ℝ)*X 1 2+(1549187697/2500000000 : ℝ)*X 2 0+(5631512933/10000000000 : ℝ)*X 2 1+(-25703697/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-1265585813/10000000000 : ℝ)*X 0 0+(4324763511/10000000000 : ℝ)*X 0 1+(-857574359/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((1007592113/2500000000 : ℝ)*X 1 0+(-328265909/2000000000 : ℝ)*X 1 1+(-688470701/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((290901427/500000000 : ℝ)*X 2 0+(272520059/500000000 : ℝ)*X 2 1+(640240627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((977285791/1250000000 : ℝ)*X 0 0+(1886749397/5000000000 : ℝ)*X 0 1+(-31421527/2000000000 : ℝ)*X 0 2+(977285791/1250000000 : ℝ)*X 1 0+(1886749397/5000000000 : ℝ)*X 1 1+(-31421527/2000000000 : ℝ)*X 1 2+(977285791/1250000000 : ℝ)*X 2 0+(1886749397/5000000000 : ℝ)*X 2 1+(-31421527/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-98131643/1000000000 : ℝ)*X 0 0+(2726096041/5000000000 : ℝ)*X 0 1+(-599057217/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((5828718407/10000000000 : ℝ)*X 1 0+(-279055887/2000000000 : ℝ)*X 1 1+(-2683351831/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((258210741/625000000 : ℝ)*X 2 0+(205557143/312500000 : ℝ)*X 2 1+(99043661/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((1631255549/2000000000 : ℝ)*X 0 0+(3291614299/10000000000 : ℝ)*X 0 1+(-51951277/2000000000 : ℝ)*X 0 2+(1631255549/2000000000 : ℝ)*X 1 0+(3291614299/10000000000 : ℝ)*X 1 1+(-51951277/2000000000 : ℝ)*X 1 2+(1631255549/2000000000 : ℝ)*X 2 0+(3291614299/10000000000 : ℝ)*X 2 1+(-51951277/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301060_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((6787/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6787/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15378589581762557376421679789/1366491013487500000000000000000000 : ℝ) := by norm_num
    linear_combination (228623/200000000000 : ℝ)*(base5) + (359973/62500000000 : ℝ)*(base39) + (2627249/1000000000000 : ℝ)*(base49) + (310524851633/1000000000000 : ℝ)*(base59) + (5140752108349/1000000000000 : ℝ)*(major_s5_0) + (5140752108349/1000000000000 : ℝ)*(major_s5_1) + (5140752108349/1000000000000 : ℝ)*(major_s5_2) + (17659743/1000000000000 : ℝ)*(sp_s5_1) + (85077933939/12500000000 : ℝ)*(sp_s5_7) + (3402639911117/500000000000 : ℝ)*(sp_s5_8) + (340305744741/50000000000 : ℝ)*(sp_s5_9) + (3475264607101/1000000000000 : ℝ)*(sp_s5_13) + (117154143/125000000000 : ℝ)*(sp_s5_15) + (24192683/200000000000 : ℝ)*(sp_s5_23) + (434408218777/125000000000 : ℝ)*(f.failure) + (85077933939/12500000000 : ℝ)*(f.sum) + (41331906213877666261/164802936300000000000000000000000 : ℝ)*base62 + (1449946081023249/3231050000000000000000000000 : ℝ)*base65 + (153234320139301/3825450000000000000000000000 : ℝ)*base66 + (142389412393773/323105000000000000000000000 : ℝ)*base68 + (567319165444825607/1285957900000000000000000000000 : ℝ)*base71 + (12234385893333/19900000000000000000000000 : ℝ)*base73 + (79758446626591/2550300000000000000000000000 : ℝ)*base74 + (256677848509/3980000000000000000000000 : ℝ)*base77 + (753210247643855659/1522529100000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (403/781250000000000 : ℝ)*base87 + (403/781250000000000 : ℝ)*base89 + (403/781250000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58213/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(58213/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (131397132058592158379901447/9696122566000000000000000000000 : ℝ) := by norm_num
    linear_combination (1354211/1000000000000 : ℝ)*(base5) + (1288481/500000000000 : ℝ)*(base18) + (6027877/1000000000000 : ℝ)*(base59) + (498851609991/100000000000 : ℝ)*(major_s5_0) + (498851609991/100000000000 : ℝ)*(major_s5_1) + (498851609991/100000000000 : ℝ)*(major_s5_2) + (26111367/1000000000000 : ℝ)*(sp_s5_2) + (7579059/1000000000000 : ℝ)*(sp_s5_6) + (2283453/31250000000 : ℝ)*(sp_s5_7) + (132092077561/20000000000 : ℝ)*(sp_s5_14) + (1612469329/244140625 : ℝ)*(sp_s5_15) + (660465219139/100000000000 : ℝ)*(sp_s5_16) + (84304789671/25000000000 : ℝ)*(sp_s5_20) + (15021399/100000000000 : ℝ)*(sp_s5_27) + (33723507341/10000000000 : ℝ)*(f.failure) + (3302338474273/500000000000 : ℝ)*(f.sum) + (105365303620494451/549343121000000000000000000000 : ℝ)*base62 + (19422696620443/25848400000000000000000000 : ℝ)*base65 + (25459754036983/63757500000000000000000000 : ℝ)*base66 + (35606532744491/129242000000000000000000000 : ℝ)*base69 + (939961644091079781/3030038301875000000000000000000 : ℝ)*base71 + (233277260230953/750230000000000000000000000 : ℝ)*base72 + (19396094438399/85010000000000000000000000 : ℝ)*base75 + (250878728902721/750230000000000000000000000 : ℝ)*base77 + (186420373008901661/2391639461250000000000000000000 : ℝ)*base79 + (21/250000000000000 : ℝ)*base87 + (21/250000000000000 : ℝ)*base89 + (21/250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10371/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10371/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5287087900360635170561242874737/1030334224169575000000000000000000000 : ℝ) := by norm_num
    linear_combination (2583819/500000000000 : ℝ)*(base11) + (65753322427/200000000000 : ℝ)*(base39) + (373021/500000000000 : ℝ)*(base50) + (3832212527521/1000000000000 : ℝ)*(major_s5_0) + (3832212527521/1000000000000 : ℝ)*(major_s5_1) + (3832212527521/1000000000000 : ℝ)*(major_s5_2) + (2406297/250000000000 : ℝ)*(sp_s5_0) + (2227003/500000000000 : ℝ)*(sp_s5_1) + (48189489/1000000000000 : ℝ)*(sp_s5_9) + (3390163/500000000000 : ℝ)*(sp_s5_20) + (5073745422343/1000000000000 : ℝ)*(sp_s5_21) + (5073755761163/1000000000000 : ℝ)*(sp_s5_22) + (63421400321/12500000000 : ℝ)*(sp_s5_23) + (518131269813/200000000000 : ℝ)*(sp_s5_27) + (161916445587/62500000000 : ℝ)*(f.failure) + (5073760215169/1000000000000 : ℝ)*(f.sum) + (104772462594971877461/164802936300000000000000000000000 : ℝ)*base63 + (168123192933579/3231050000000000000000000000 : ℝ)*base64 + (1584185672701451/3825450000000000000000000000 : ℝ)*base67 + (75252037341273/646210000000000000000000000 : ℝ)*base69 + (110428270765169863531/484806128300000000000000000000000 : ℝ)*base71 + (686742801275381/7502300000000000000000000000 : ℝ)*base72 + (425562352894151/2550300000000000000000000000 : ℝ)*base75 + (320233760580119/1500460000000000000000000000 : ℝ)*base76 + (349383872416515359863/573993470700000000000000000000000 : ℝ)*base78 + (2569/3125000000000000 : ℝ)*base87 + (2569/3125000000000000 : ℝ)*base89 + (2569/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev4 : (0 : ℝ) ≤ ((75023/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75023/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76509/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76509/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64621/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-64621/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6787/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6787/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58213/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(58213/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10371/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10371/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301060_s5 p hpa hpb X hX hprev4

#print axioms solution

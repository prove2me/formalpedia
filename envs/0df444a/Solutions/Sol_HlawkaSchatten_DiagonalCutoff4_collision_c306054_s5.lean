-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306054_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:56:05.204+00:00
-- url     : https://prove2.me/submissions/9aa233a0-5acd-4d60-a039-77d22631cda5

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
theorem collision_support_c306054_s5_s5_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1901271431/10000000000 : ℝ)*x 0 + (2277925043/5000000000 : ℝ)*x 1 + (-3069072699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1901271431/10000000000 : ℝ)^17 ≤ (2281610676363/20000000000000 : ℝ)^13 := by
    have hnat : (1901271431 : ℕ)^17*20000000000000^13 ≤ 2281610676363^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901271431 10000000000 2281610676363 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2277925043/5000000000 : ℝ)^17 ≤ (8942395462489/25000000000000 : ℝ)^13 := by
    have hnat : (2277925043 : ℕ)^17*25000000000000^13 ≤ 8942395462489^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277925043 5000000000 8942395462489 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3069072699/5000000000 : ℝ)^17 ≤ (3301397797011/6250000000000 : ℝ)^13 := by
    have hnat : (3069072699 : ℕ)^17*6250000000000^13 ≤ 3301397797011^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3069072699 5000000000 3301397797011 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1901271431/10000000000 : ℝ), (2277925043/5000000000 : ℝ), (-3069072699/5000000000 : ℝ)] ![(2281610676363/20000000000000 : ℝ), (8942395462489/25000000000000 : ℝ), (3301397797011/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1901271431/10000000000 : ℝ)|^17 ≤ (2281610676363/20000000000000 : ℝ)^13
        have hw : |(-1901271431/10000000000 : ℝ)|=(1901271431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2277925043/5000000000 : ℝ)|^17 ≤ (8942395462489/25000000000000 : ℝ)^13
        have hw : |(2277925043/5000000000 : ℝ)|=(2277925043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3069072699/5000000000 : ℝ)|^17 ≤ (3301397797011/6250000000000 : ℝ)^13
        have hw : |(-3069072699/5000000000 : ℝ)|=(3069072699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s5_s5_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2717283697/5000000000 : ℝ)*x 0 + (-21777391/78125000 : ℝ)*x 1 + (-286971131/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2717283697/5000000000 : ℝ)^17 ≤ (45048183144793/100000000000000 : ℝ)^13 := by
    have hnat : (2717283697 : ℕ)^17*100000000000000^13 ≤ 45048183144793^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717283697 5000000000 45048183144793 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21777391/78125000 : ℝ)^17 ≤ (2351922496477/12500000000000 : ℝ)^13 := by
    have hnat : (21777391 : ℕ)^17*12500000000000^13 ≤ 2351922496477^13*78125000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21777391 78125000 2351922496477 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (286971131/625000000 : ℝ)^17 ≤ (36136436873531/100000000000000 : ℝ)^13 := by
    have hnat : (286971131 : ℕ)^17*100000000000000^13 ≤ 36136436873531^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286971131 625000000 36136436873531 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2717283697/5000000000 : ℝ), (-21777391/78125000 : ℝ), (-286971131/625000000 : ℝ)] ![(45048183144793/100000000000000 : ℝ), (2351922496477/12500000000000 : ℝ), (36136436873531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2717283697/5000000000 : ℝ)|^17 ≤ (45048183144793/100000000000000 : ℝ)^13
        have hw : |(2717283697/5000000000 : ℝ)|=(2717283697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21777391/78125000 : ℝ)|^17 ≤ (2351922496477/12500000000000 : ℝ)^13
        have hw : |(-21777391/78125000 : ℝ)|=(21777391/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-286971131/625000000 : ℝ)|^17 ≤ (36136436873531/100000000000000 : ℝ)^13
        have hw : |(-286971131/625000000 : ℝ)|=(286971131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s5_s5_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (314933757/625000000 : ℝ)*x 0 + (314599127/625000000 : ℝ)*x 1 + (1372414873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (314933757/625000000 : ℝ)^17 ≤ (40808558788677/100000000000000 : ℝ)^13 := by
    have hnat : (314933757 : ℕ)^17*100000000000000^13 ≤ 40808558788677^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314933757 625000000 40808558788677 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314599127/625000000 : ℝ)^17 ≤ (40751865523639/100000000000000 : ℝ)^13 := by
    have hnat : (314599127 : ℕ)^17*100000000000000^13 ≤ 40751865523639^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314599127 625000000 40751865523639 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372414873/5000000000 : ℝ)^17 ≤ (18439575667241/100000000000000 : ℝ)^13 := by
    have hnat : (1372414873 : ℕ)^17*100000000000000^13 ≤ 18439575667241^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372414873 5000000000 18439575667241 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(314933757/625000000 : ℝ), (314599127/625000000 : ℝ), (1372414873/5000000000 : ℝ)] ![(40808558788677/100000000000000 : ℝ), (40751865523639/100000000000000 : ℝ), (18439575667241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(314933757/625000000 : ℝ)|^17 ≤ (40808558788677/100000000000000 : ℝ)^13
        have hw : |(314933757/625000000 : ℝ)|=(314933757/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(314599127/625000000 : ℝ)|^17 ≤ (40751865523639/100000000000000 : ℝ)^13
        have hw : |(314599127/625000000 : ℝ)|=(314599127/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372414873/5000000000 : ℝ)|^17 ≤ (18439575667241/100000000000000 : ℝ)^13
        have hw : |(1372414873/5000000000 : ℝ)|=(1372414873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s5_s5_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1259559151/2500000000 : ℝ)*x 0 + (1006745303/2000000000 : ℝ)*x 1 + (-1372754249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1259559151/2500000000 : ℝ)^17 ≤ (10200277106813/25000000000000 : ℝ)^13 := by
    have hnat : (1259559151 : ℕ)^17*25000000000000^13 ≤ 10200277106813^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259559151 2500000000 10200277106813 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006745303/2000000000 : ℝ)^17 ≤ (40753352832637/100000000000000 : ℝ)^13 := by
    have hnat : (1006745303 : ℕ)^17*100000000000000^13 ≤ 40753352832637^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006745303 2000000000 40753352832637 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372754249/5000000000 : ℝ)^17 ≤ (2305692340123/12500000000000 : ℝ)^13 := by
    have hnat : (1372754249 : ℕ)^17*12500000000000^13 ≤ 2305692340123^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372754249 5000000000 2305692340123 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1259559151/2500000000 : ℝ), (1006745303/2000000000 : ℝ), (-1372754249/5000000000 : ℝ)] ![(10200277106813/25000000000000 : ℝ), (40753352832637/100000000000000 : ℝ), (2305692340123/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1259559151/2500000000 : ℝ)|^17 ≤ (10200277106813/25000000000000 : ℝ)^13
        have hw : |(1259559151/2500000000 : ℝ)|=(1259559151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1006745303/2000000000 : ℝ)|^17 ≤ (40753352832637/100000000000000 : ℝ)^13
        have hw : |(1006745303/2000000000 : ℝ)|=(1006745303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1372754249/5000000000 : ℝ)|^17 ≤ (2305692340123/12500000000000 : ℝ)^13
        have hw : |(-1372754249/5000000000 : ℝ)|=(1372754249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s5_s5_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1870125121/10000000000 : ℝ)*x 0 + (1098014283/2500000000 : ℝ)*x 1 + (-1576923733/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1870125121/10000000000 : ℝ)^17 ≤ (2791070953167/25000000000000 : ℝ)^13 := by
    have hnat : (1870125121 : ℕ)^17*25000000000000^13 ≤ 2791070953167^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870125121 10000000000 2791070953167 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098014283/2500000000 : ℝ)^17 ≤ (34097274602447/100000000000000 : ℝ)^13 := by
    have hnat : (1098014283 : ℕ)^17*100000000000000^13 ≤ 34097274602447^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098014283 2500000000 34097274602447 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1576923733/2500000000 : ℝ)^17 ≤ (547384415721/1000000000000 : ℝ)^13 := by
    have hnat : (1576923733 : ℕ)^17*1000000000000^13 ≤ 547384415721^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1576923733 2500000000 547384415721 1000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1870125121/10000000000 : ℝ), (1098014283/2500000000 : ℝ), (-1576923733/2500000000 : ℝ)] ![(2791070953167/25000000000000 : ℝ), (34097274602447/100000000000000 : ℝ), (547384415721/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1870125121/10000000000 : ℝ)|^17 ≤ (2791070953167/25000000000000 : ℝ)^13
        have hw : |(-1870125121/10000000000 : ℝ)|=(1870125121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098014283/2500000000 : ℝ)|^17 ≤ (34097274602447/100000000000000 : ℝ)^13
        have hw : |(1098014283/2500000000 : ℝ)|=(1098014283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1576923733/2500000000 : ℝ)|^17 ≤ (547384415721/1000000000000 : ℝ)^13
        have hw : |(-1576923733/2500000000 : ℝ)|=(1576923733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s5_s5_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5384464513/10000000000 : ℝ)*x 0 + (-1262223861/5000000000 : ℝ)*x 1 + (-4864040379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384464513/10000000000 : ℝ)^17 ≤ (2225292707011/5000000000000 : ℝ)^13 := by
    have hnat : (5384464513 : ℕ)^17*5000000000000^13 ≤ 2225292707011^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384464513 10000000000 2225292707011 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1262223861/5000000000 : ℝ)^17 ≤ (4131974041071/25000000000000 : ℝ)^13 := by
    have hnat : (1262223861 : ℕ)^17*25000000000000^13 ≤ 4131974041071^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262223861 5000000000 4131974041071 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4864040379/10000000000 : ℝ)^17 ≤ (38966249681739/100000000000000 : ℝ)^13 := by
    have hnat : (4864040379 : ℕ)^17*100000000000000^13 ≤ 38966249681739^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4864040379 10000000000 38966249681739 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384464513/10000000000 : ℝ), (-1262223861/5000000000 : ℝ), (-4864040379/10000000000 : ℝ)] ![(2225292707011/5000000000000 : ℝ), (4131974041071/25000000000000 : ℝ), (38966249681739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384464513/10000000000 : ℝ)|^17 ≤ (2225292707011/5000000000000 : ℝ)^13
        have hw : |(5384464513/10000000000 : ℝ)|=(5384464513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1262223861/5000000000 : ℝ)|^17 ≤ (4131974041071/25000000000000 : ℝ)^13
        have hw : |(-1262223861/5000000000 : ℝ)|=(1262223861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4864040379/10000000000 : ℝ)|^17 ≤ (38966249681739/100000000000000 : ℝ)^13
        have hw : |(-4864040379/10000000000 : ℝ)|=(4864040379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s5_s5_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4964259739/10000000000 : ℝ)*x 0 + (1331269321/2500000000 : ℝ)*x 1 + (1238068399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4964259739/10000000000 : ℝ)^17 ≤ (8003892745023/20000000000000 : ℝ)^13 := by
    have hnat : (4964259739 : ℕ)^17*20000000000000^13 ≤ 8003892745023^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4964259739 10000000000 8003892745023 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1331269321/2500000000 : ℝ)^17 ≤ (21932518723611/50000000000000 : ℝ)^13 := by
    have hnat : (1331269321 : ℕ)^17*50000000000000^13 ≤ 21932518723611^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331269321 2500000000 21932518723611 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1238068399/5000000000 : ℝ)^17 ≤ (4028874703407/25000000000000 : ℝ)^13 := by
    have hnat : (1238068399 : ℕ)^17*25000000000000^13 ≤ 4028874703407^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238068399 5000000000 4028874703407 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4964259739/10000000000 : ℝ), (1331269321/2500000000 : ℝ), (1238068399/5000000000 : ℝ)] ![(8003892745023/20000000000000 : ℝ), (21932518723611/50000000000000 : ℝ), (4028874703407/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4964259739/10000000000 : ℝ)|^17 ≤ (8003892745023/20000000000000 : ℝ)^13
        have hw : |(4964259739/10000000000 : ℝ)|=(4964259739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1331269321/2500000000 : ℝ)|^17 ≤ (21932518723611/50000000000000 : ℝ)^13
        have hw : |(1331269321/2500000000 : ℝ)|=(1331269321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1238068399/5000000000 : ℝ)|^17 ≤ (4028874703407/25000000000000 : ℝ)^13
        have hw : |(1238068399/5000000000 : ℝ)|=(1238068399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s5_s5_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2511031667/5000000000 : ℝ)*x 0 + (1332292567/2500000000 : ℝ)*x 1 + (-1199427911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2511031667/5000000000 : ℝ)^17 ≤ (10157479239947/25000000000000 : ℝ)^13 := by
    have hnat : (2511031667 : ℕ)^17*25000000000000^13 ≤ 10157479239947^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511031667 5000000000 10157479239947 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1332292567/2500000000 : ℝ)^17 ≤ (43909132467679/100000000000000 : ℝ)^13 := by
    have hnat : (1332292567 : ℕ)^17*100000000000000^13 ≤ 43909132467679^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1332292567 2500000000 43909132467679 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199427911/5000000000 : ℝ)^17 ≤ (3092190112521/20000000000000 : ℝ)^13 := by
    have hnat : (1199427911 : ℕ)^17*20000000000000^13 ≤ 3092190112521^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199427911 5000000000 3092190112521 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2511031667/5000000000 : ℝ), (1332292567/2500000000 : ℝ), (-1199427911/5000000000 : ℝ)] ![(10157479239947/25000000000000 : ℝ), (43909132467679/100000000000000 : ℝ), (3092190112521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2511031667/5000000000 : ℝ)|^17 ≤ (10157479239947/25000000000000 : ℝ)^13
        have hw : |(2511031667/5000000000 : ℝ)|=(2511031667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1332292567/2500000000 : ℝ)|^17 ≤ (43909132467679/100000000000000 : ℝ)^13
        have hw : |(1332292567/2500000000 : ℝ)|=(1332292567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1199427911/5000000000 : ℝ)|^17 ≤ (3092190112521/20000000000000 : ℝ)^13
        have hw : |(-1199427911/5000000000 : ℝ)|=(1199427911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s5_s5_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1678930637/10000000000 : ℝ)*x 0 + (4553604113/10000000000 : ℝ)*x 1 + (-6291764387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1678930637/10000000000 : ℝ)^17 ≤ (9695747432389/100000000000000 : ℝ)^13 := by
    have hnat : (1678930637 : ℕ)^17*100000000000000^13 ≤ 9695747432389^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678930637 10000000000 9695747432389 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4553604113/10000000000 : ℝ)^17 ≤ (35746523852077/100000000000000 : ℝ)^13 := by
    have hnat : (4553604113 : ℕ)^17*100000000000000^13 ≤ 35746523852077^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4553604113 10000000000 35746523852077 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6291764387/10000000000 : ℝ)^17 ≤ (27278864352881/50000000000000 : ℝ)^13 := by
    have hnat : (6291764387 : ℕ)^17*50000000000000^13 ≤ 27278864352881^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6291764387 10000000000 27278864352881 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1678930637/10000000000 : ℝ), (4553604113/10000000000 : ℝ), (-6291764387/10000000000 : ℝ)] ![(9695747432389/100000000000000 : ℝ), (35746523852077/100000000000000 : ℝ), (27278864352881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1678930637/10000000000 : ℝ)|^17 ≤ (9695747432389/100000000000000 : ℝ)^13
        have hw : |(-1678930637/10000000000 : ℝ)|=(1678930637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4553604113/10000000000 : ℝ)|^17 ≤ (35746523852077/100000000000000 : ℝ)^13
        have hw : |(4553604113/10000000000 : ℝ)|=(4553604113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6291764387/10000000000 : ℝ)|^17 ≤ (27278864352881/50000000000000 : ℝ)^13
        have hw : |(-6291764387/10000000000 : ℝ)|=(6291764387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s5_s5_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5231125379/10000000000 : ℝ)*x 0 + (-338008153/1250000000 : ℝ)*x 1 + (-4873175519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5231125379/10000000000 : ℝ)^17 ≤ (21427870820733/50000000000000 : ℝ)^13 := by
    have hnat : (5231125379 : ℕ)^17*50000000000000^13 ≤ 21427870820733^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231125379 10000000000 21427870820733 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338008153/1250000000 : ℝ)^17 ≤ (9041140480919/50000000000000 : ℝ)^13 := by
    have hnat : (338008153 : ℕ)^17*50000000000000^13 ≤ 9041140480919^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338008153 1250000000 9041140480919 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4873175519/10000000000 : ℝ)^17 ≤ (9765494345503/25000000000000 : ℝ)^13 := by
    have hnat : (4873175519 : ℕ)^17*25000000000000^13 ≤ 9765494345503^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4873175519 10000000000 9765494345503 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5231125379/10000000000 : ℝ), (-338008153/1250000000 : ℝ), (-4873175519/10000000000 : ℝ)] ![(21427870820733/50000000000000 : ℝ), (9041140480919/50000000000000 : ℝ), (9765494345503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5231125379/10000000000 : ℝ)|^17 ≤ (21427870820733/50000000000000 : ℝ)^13
        have hw : |(5231125379/10000000000 : ℝ)|=(5231125379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-338008153/1250000000 : ℝ)|^17 ≤ (9041140480919/50000000000000 : ℝ)^13
        have hw : |(-338008153/1250000000 : ℝ)|=(338008153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4873175519/10000000000 : ℝ)|^17 ≤ (9765494345503/25000000000000 : ℝ)^13
        have hw : |(-4873175519/10000000000 : ℝ)|=(4873175519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s5_s5_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1333902439/2500000000 : ℝ)*x 0 + (4960863841/10000000000 : ℝ)*x 1 + (2467002707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1333902439/2500000000 : ℝ)^17 ≤ (43978528217527/100000000000000 : ℝ)^13 := by
    have hnat : (1333902439 : ℕ)^17*100000000000000^13 ≤ 43978528217527^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333902439 2500000000 43978528217527 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4960863841/10000000000 : ℝ)^17 ≤ (19991833996099/50000000000000 : ℝ)^13 := by
    have hnat : (4960863841 : ℕ)^17*50000000000000^13 ≤ 19991833996099^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4960863841 10000000000 19991833996099 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2467002707/10000000000 : ℝ)^17 ≤ (16037803777587/100000000000000 : ℝ)^13 := by
    have hnat : (2467002707 : ℕ)^17*100000000000000^13 ≤ 16037803777587^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2467002707 10000000000 16037803777587 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1333902439/2500000000 : ℝ), (4960863841/10000000000 : ℝ), (2467002707/10000000000 : ℝ)] ![(43978528217527/100000000000000 : ℝ), (19991833996099/50000000000000 : ℝ), (16037803777587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1333902439/2500000000 : ℝ)|^17 ≤ (43978528217527/100000000000000 : ℝ)^13
        have hw : |(1333902439/2500000000 : ℝ)|=(1333902439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4960863841/10000000000 : ℝ)|^17 ≤ (19991833996099/50000000000000 : ℝ)^13
        have hw : |(4960863841/10000000000 : ℝ)|=(4960863841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2467002707/10000000000 : ℝ)|^17 ≤ (16037803777587/100000000000000 : ℝ)^13
        have hw : |(2467002707/10000000000 : ℝ)|=(2467002707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s5_s5_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1064132359/2000000000 : ℝ)*x 0 + (5004215067/10000000000 : ℝ)*x 1 + (-2432051697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064132359/2000000000 : ℝ)^17 ≤ (43817479669843/100000000000000 : ℝ)^13 := by
    have hnat : (1064132359 : ℕ)^17*100000000000000^13 ≤ 43817479669843^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064132359 2000000000 43817479669843 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5004215067/10000000000 : ℝ)^17 ≤ (5055149091581/12500000000000 : ℝ)^13 := by
    have hnat : (5004215067 : ℕ)^17*12500000000000^13 ≤ 5055149091581^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5004215067 10000000000 5055149091581 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2432051697/10000000000 : ℝ)^17 ≤ (491916486973/3125000000000 : ℝ)^13 := by
    have hnat : (2432051697 : ℕ)^17*3125000000000^13 ≤ 491916486973^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2432051697 10000000000 491916486973 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1064132359/2000000000 : ℝ), (5004215067/10000000000 : ℝ), (-2432051697/10000000000 : ℝ)] ![(43817479669843/100000000000000 : ℝ), (5055149091581/12500000000000 : ℝ), (491916486973/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1064132359/2000000000 : ℝ)|^17 ≤ (43817479669843/100000000000000 : ℝ)^13
        have hw : |(1064132359/2000000000 : ℝ)|=(1064132359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5004215067/10000000000 : ℝ)|^17 ≤ (5055149091581/12500000000000 : ℝ)^13
        have hw : |(5004215067/10000000000 : ℝ)|=(5004215067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2432051697/10000000000 : ℝ)|^17 ≤ (491916486973/3125000000000 : ℝ)^13
        have hw : |(-2432051697/10000000000 : ℝ)|=(2432051697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s5_s5_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-96786217/625000000 : ℝ)*x 0 + (4843069213/10000000000 : ℝ)*x 1 + (-6112145781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (96786217/625000000 : ℝ)^17 ≤ (1744665857711/20000000000000 : ℝ)^13 := by
    have hnat : (96786217 : ℕ)^17*20000000000000^13 ≤ 1744665857711^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96786217 625000000 1744665857711 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4843069213/10000000000 : ℝ)^17 ≤ (38746700848901/100000000000000 : ℝ)^13 := by
    have hnat : (4843069213 : ℕ)^17*100000000000000^13 ≤ 38746700848901^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4843069213 10000000000 38746700848901 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6112145781/10000000000 : ℝ)^17 ≤ (10505993968349/20000000000000 : ℝ)^13 := by
    have hnat : (6112145781 : ℕ)^17*20000000000000^13 ≤ 10505993968349^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6112145781 10000000000 10505993968349 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-96786217/625000000 : ℝ), (4843069213/10000000000 : ℝ), (-6112145781/10000000000 : ℝ)] ![(1744665857711/20000000000000 : ℝ), (38746700848901/100000000000000 : ℝ), (10505993968349/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-96786217/625000000 : ℝ)|^17 ≤ (1744665857711/20000000000000 : ℝ)^13
        have hw : |(-96786217/625000000 : ℝ)|=(96786217/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4843069213/10000000000 : ℝ)|^17 ≤ (38746700848901/100000000000000 : ℝ)^13
        have hw : |(4843069213/10000000000 : ℝ)|=(4843069213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6112145781/10000000000 : ℝ)|^17 ≤ (10505993968349/20000000000000 : ℝ)^13
        have hw : |(-6112145781/10000000000 : ℝ)|=(6112145781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s5_s5_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5791068897/10000000000 : ℝ)*x 0 + (-1252050129/5000000000 : ℝ)*x 1 + (-4450824383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5791068897/10000000000 : ℝ)^17 ≤ (48950983123611/100000000000000 : ℝ)^13 := by
    have hnat : (5791068897 : ℕ)^17*100000000000000^13 ≤ 48950983123611^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5791068897 10000000000 48950983123611 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1252050129/5000000000 : ℝ)^17 ≤ (16353905007541/100000000000000 : ℝ)^13 := by
    have hnat : (1252050129 : ℕ)^17*100000000000000^13 ≤ 16353905007541^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252050129 5000000000 16353905007541 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4450824383/10000000000 : ℝ)^17 ≤ (34695111856973/100000000000000 : ℝ)^13 := by
    have hnat : (4450824383 : ℕ)^17*100000000000000^13 ≤ 34695111856973^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4450824383 10000000000 34695111856973 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5791068897/10000000000 : ℝ), (-1252050129/5000000000 : ℝ), (-4450824383/10000000000 : ℝ)] ![(48950983123611/100000000000000 : ℝ), (16353905007541/100000000000000 : ℝ), (34695111856973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5791068897/10000000000 : ℝ)|^17 ≤ (48950983123611/100000000000000 : ℝ)^13
        have hw : |(5791068897/10000000000 : ℝ)|=(5791068897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1252050129/5000000000 : ℝ)|^17 ≤ (16353905007541/100000000000000 : ℝ)^13
        have hw : |(-1252050129/5000000000 : ℝ)|=(1252050129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4450824383/10000000000 : ℝ)|^17 ≤ (34695111856973/100000000000000 : ℝ)^13
        have hw : |(-4450824383/10000000000 : ℝ)|=(4450824383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s5_s5_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2508209299/5000000000 : ℝ)*x 0 + (5011015471/10000000000 : ℝ)*x 1 + (699744859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2508209299/5000000000 : ℝ)^17 ≤ (40570208230479/100000000000000 : ℝ)^13 := by
    have hnat : (2508209299 : ℕ)^17*100000000000000^13 ≤ 40570208230479^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508209299 5000000000 40570208230479 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5011015471/10000000000 : ℝ)^17 ≤ (40513074547163/100000000000000 : ℝ)^13 := by
    have hnat : (5011015471 : ℕ)^17*100000000000000^13 ≤ 40513074547163^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5011015471 10000000000 40513074547163 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (699744859/2500000000 : ℝ)^17 ≤ (18916717215089/100000000000000 : ℝ)^13 := by
    have hnat : (699744859 : ℕ)^17*100000000000000^13 ≤ 18916717215089^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699744859 2500000000 18916717215089 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2508209299/5000000000 : ℝ), (5011015471/10000000000 : ℝ), (699744859/2500000000 : ℝ)] ![(40570208230479/100000000000000 : ℝ), (40513074547163/100000000000000 : ℝ), (18916717215089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2508209299/5000000000 : ℝ)|^17 ≤ (40570208230479/100000000000000 : ℝ)^13
        have hw : |(2508209299/5000000000 : ℝ)|=(2508209299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5011015471/10000000000 : ℝ)|^17 ≤ (40513074547163/100000000000000 : ℝ)^13
        have hw : |(5011015471/10000000000 : ℝ)|=(5011015471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(699744859/2500000000 : ℝ)|^17 ≤ (18916717215089/100000000000000 : ℝ)^13
        have hw : |(699744859/2500000000 : ℝ)|=(699744859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s5_s5_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2545308243/5000000000 : ℝ)*x 0 + (635775397/1250000000 : ℝ)*x 1 + (-2618010917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2545308243/5000000000 : ℝ)^17 ≤ (20678350167367/50000000000000 : ℝ)^13 := by
    have hnat : (2545308243 : ℕ)^17*50000000000000^13 ≤ 20678350167367^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2545308243 5000000000 20678350167367 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635775397/1250000000 : ℝ)^17 ≤ (20654910169449/50000000000000 : ℝ)^13 := by
    have hnat : (635775397 : ℕ)^17*50000000000000^13 ≤ 20654910169449^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635775397 1250000000 20654910169449 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618010917/10000000000 : ℝ)^17 ≤ (8666739656859/50000000000000 : ℝ)^13 := by
    have hnat : (2618010917 : ℕ)^17*50000000000000^13 ≤ 8666739656859^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618010917 10000000000 8666739656859 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2545308243/5000000000 : ℝ), (635775397/1250000000 : ℝ), (-2618010917/10000000000 : ℝ)] ![(20678350167367/50000000000000 : ℝ), (20654910169449/50000000000000 : ℝ), (8666739656859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2545308243/5000000000 : ℝ)|^17 ≤ (20678350167367/50000000000000 : ℝ)^13
        have hw : |(2545308243/5000000000 : ℝ)|=(2545308243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635775397/1250000000 : ℝ)|^17 ≤ (20654910169449/50000000000000 : ℝ)^13
        have hw : |(635775397/1250000000 : ℝ)|=(635775397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2618010917/10000000000 : ℝ)|^17 ≤ (8666739656859/50000000000000 : ℝ)^13
        have hw : |(-2618010917/10000000000 : ℝ)|=(2618010917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306054_s5 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev4 : (0 : ℝ) ≤ ((33199/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33199/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17317/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17317/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11221/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11221/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((19751/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19751/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10417/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10417/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-82/625 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-82/625 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (33199/100000 : ℝ) ^ (67/16 : ℝ) ≤ (493947681948593421/50000000000000000000 : ℝ) := by
    have hpowers : (33199/100000 : ℝ)^67 ≤ (493947681948593421/50000000000000000000 : ℝ)^16 := by
      have hnat : (33199 : ℕ)^67*50000000000000000000^16 ≤ 493947681948593421^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33199 100000 493947681948593421 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33199/100000 : ℝ)) (X := (493947681948593421/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner0a : (50493947681948593421/50000000000000000000 : ℝ) ≤ (1252937917528191/1250000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50493947681948593421/50000000000000000000 : ℝ)^16 ≤ (1252937917528191/1250000000000000 : ℝ)^67 := by
      have hnat : (50493947681948593421 : ℕ)^16*1250000000000000^67 ≤ 1252937917528191^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50493947681948593421 50000000000000000000 1252937917528191 1250000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252937917528191/1250000000000000 : ℝ)) (X := (50493947681948593421/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner0b : (25493947681948593421/25000000000000000000 : ℝ) ≤ (2511708078775133/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (25493947681948593421/25000000000000000000 : ℝ)^16 ≤ (2511708078775133/2500000000000000 : ℝ)^67 := by
      have hnat : (25493947681948593421 : ℕ)^16*2500000000000000^67 ≤ 2511708078775133^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25493947681948593421 25000000000000000000 2511708078775133 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511708078775133/2500000000000000 : ℝ)) (X := (25493947681948593421/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(2937917528191/414987500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(5832243718751/829975000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (33199/100000 : ℝ)) (alpha := (2937917528191/414987500000000 : ℝ)) (beta := (5832243718751/829975000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (33199/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(2937917528191/414987500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(5832243718751/829975000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (17317/50000 : ℝ) ^ (67/16 : ℝ) ≤ (18428389540819281/1562500000000000000 : ℝ) := by
    have hpowers : (17317/50000 : ℝ)^67 ≤ (18428389540819281/1562500000000000000 : ℝ)^16 := by
      have hnat : (17317 : ℕ)^67*1562500000000000000^16 ≤ 18428389540819281^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17317 50000 18428389540819281 1562500000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17317/50000 : ℝ)) (X := (18428389540819281/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner1a : (1580928389540819281/1562500000000000000 : ℝ) ≤ (5014019810084179/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (1580928389540819281/1562500000000000000 : ℝ)^16 ≤ (5014019810084179/5000000000000000 : ℝ)^67 := by
      have hnat : (1580928389540819281 : ℕ)^16*5000000000000000^67 ≤ 5014019810084179^67*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1580928389540819281 1562500000000000000 5014019810084179 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014019810084179/5000000000000000 : ℝ)) (X := (1580928389540819281/1562500000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner1b : (799678389540819281/781250000000000000 : ℝ) ≤ (314244735548643/312500000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (799678389540819281/781250000000000000 : ℝ)^16 ≤ (314244735548643/312500000000000 : ℝ)^67 := by
      have hnat : (799678389540819281 : ℕ)^16*312500000000000^67 ≤ 314244735548643^67*781250000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        799678389540819281 781250000000000000 314244735548643 312500000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (314244735548643/312500000000000 : ℝ)) (X := (799678389540819281/781250000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(14019810084179/1731700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(13895958694109/1731700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (17317/50000 : ℝ)) (alpha := (14019810084179/1731700000000000 : ℝ)) (beta := (13895958694109/1731700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (17317/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(14019810084179/1731700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(13895958694109/1731700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (11221/50000 : ℝ) ^ (67/16 : ℝ) ≤ (191677119511477149/100000000000000000000 : ℝ) := by
    have hpowers : (11221/50000 : ℝ)^67 ≤ (191677119511477149/100000000000000000000 : ℝ)^16 := by
      have hnat : (11221 : ℕ)^67*100000000000000000000^16 ≤ 191677119511477149^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11221 50000 191677119511477149 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11221/50000 : ℝ)) (X := (191677119511477149/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner2a : (100191677119511477149/100000000000000000000 : ℝ) ≤ (5002287014266973/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (100191677119511477149/100000000000000000000 : ℝ)^16 ≤ (5002287014266973/5000000000000000 : ℝ)^67 := by
      have hnat : (100191677119511477149 : ℕ)^16*5000000000000000^67 ≤ 5002287014266973^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100191677119511477149 100000000000000000000 5002287014266973 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002287014266973/5000000000000000 : ℝ)) (X := (100191677119511477149/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s5_corner2b : (50191677119511477149/50000000000000000000 : ℝ) ≤ (500457070050527/500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50191677119511477149/50000000000000000000 : ℝ)^16 ≤ (500457070050527/500000000000000 : ℝ)^67 := by
      have hnat : (50191677119511477149 : ℕ)^16*500000000000000^67 ≤ 500457070050527^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50191677119511477149 50000000000000000000 500457070050527 500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500457070050527/500000000000000 : ℝ)) (X := (50191677119511477149/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(2287014266973/1122100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(2283686238297/1122100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (11221/50000 : ℝ)) (alpha := (2287014266973/1122100000000000 : ℝ)) (beta := (2283686238297/1122100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (11221/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(2287014266973/1122100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(2283686238297/1122100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-1901271431/10000000000 : ℝ)*X 0 0+(2277925043/5000000000 : ℝ)*X 0 1+(-3069072699/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((2717283697/5000000000 : ℝ)*X 1 0+(-21777391/78125000 : ℝ)*X 1 1+(-286971131/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((314933757/625000000 : ℝ)*X 2 0+(314599127/625000000 : ℝ)*X 2 1+(1372414873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((1259559151/2500000000 : ℝ)*X 0 0+(1006745303/2000000000 : ℝ)*X 0 1+(-1372754249/5000000000 : ℝ)*X 0 2+(1259559151/2500000000 : ℝ)*X 1 0+(1006745303/2000000000 : ℝ)*X 1 1+(-1372754249/5000000000 : ℝ)*X 1 2+(1259559151/2500000000 : ℝ)*X 2 0+(1006745303/2000000000 : ℝ)*X 2 1+(-1372754249/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-1870125121/10000000000 : ℝ)*X 0 0+(1098014283/2500000000 : ℝ)*X 0 1+(-1576923733/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((5384464513/10000000000 : ℝ)*X 1 0+(-1262223861/5000000000 : ℝ)*X 1 1+(-4864040379/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((4964259739/10000000000 : ℝ)*X 2 0+(1331269321/2500000000 : ℝ)*X 2 1+(1238068399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((2511031667/5000000000 : ℝ)*X 0 0+(1332292567/2500000000 : ℝ)*X 0 1+(-1199427911/5000000000 : ℝ)*X 0 2+(2511031667/5000000000 : ℝ)*X 1 0+(1332292567/2500000000 : ℝ)*X 1 1+(-1199427911/5000000000 : ℝ)*X 1 2+(2511031667/5000000000 : ℝ)*X 2 0+(1332292567/2500000000 : ℝ)*X 2 1+(-1199427911/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-1678930637/10000000000 : ℝ)*X 0 0+(4553604113/10000000000 : ℝ)*X 0 1+(-6291764387/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((5231125379/10000000000 : ℝ)*X 1 0+(-338008153/1250000000 : ℝ)*X 1 1+(-4873175519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((1333902439/2500000000 : ℝ)*X 2 0+(4960863841/10000000000 : ℝ)*X 2 1+(2467002707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((1064132359/2000000000 : ℝ)*X 0 0+(5004215067/10000000000 : ℝ)*X 0 1+(-2432051697/10000000000 : ℝ)*X 0 2+(1064132359/2000000000 : ℝ)*X 1 0+(5004215067/10000000000 : ℝ)*X 1 1+(-2432051697/10000000000 : ℝ)*X 1 2+(1064132359/2000000000 : ℝ)*X 2 0+(5004215067/10000000000 : ℝ)*X 2 1+(-2432051697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-96786217/625000000 : ℝ)*X 0 0+(4843069213/10000000000 : ℝ)*X 0 1+(-6112145781/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((5791068897/10000000000 : ℝ)*X 1 0+(-1252050129/5000000000 : ℝ)*X 1 1+(-4450824383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((2508209299/5000000000 : ℝ)*X 2 0+(5011015471/10000000000 : ℝ)*X 2 1+(699744859/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((2545308243/5000000000 : ℝ)*X 0 0+(635775397/1250000000 : ℝ)*X 0 1+(-2618010917/10000000000 : ℝ)*X 0 2+(2545308243/5000000000 : ℝ)*X 1 0+(635775397/1250000000 : ℝ)*X 1 1+(-2618010917/10000000000 : ℝ)*X 1 2+(2545308243/5000000000 : ℝ)*X 2 0+(635775397/1250000000 : ℝ)*X 2 1+(-2618010917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((19751/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19751/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (99451027699551444594059847/14372677075000000000000000000000 : ℝ) := by norm_num
    linear_combination (3093566070549/1000000000000 : ℝ)*(base39) + (3178057/1000000000000 : ℝ)*(base50) + (1079801346843/1000000000000 : ℝ)*(base60) + (8590911106033/500000000000 : ℝ)*(major_s5_0) + (8590911106033/500000000000 : ℝ)*(major_s5_1) + (8590911106033/500000000000 : ℝ)*(major_s5_2) + (91306917/1000000000000 : ℝ)*(sp_s5_0) + (181405500293/7812500000 : ℝ)*(sp_s5_7) + (11609901946137/500000000000 : ℝ)*(sp_s5_8) + (11609964218047/500000000000 : ℝ)*(sp_s5_9) + (5571784147739/500000000000 : ℝ)*(sp_s5_13) + (4904859/62500000000 : ℝ)*(sp_s5_14) + (269929889/1000000000000 : ℝ)*(sp_s5_15) + (145386069/1000000000000 : ℝ)*(sp_s5_23) + (5571784147739/500000000000 : ℝ)*(f.failure) + (5805018455541/250000000000 : ℝ)*(f.sum) + (567803644707738841/1943140570000000000000000000000 : ℝ)*base62 + (190123881269629/561050000000000000000000000 : ℝ)*base64 + (397114211078133/865850000000000000000000000 : ℝ)*base67 + (18329044191971/140262500000000000000000000 : ℝ)*base69 + (3888837495636569803/18626298950000000000000000000000 : ℝ)*base71 + (166798463236367/1659950000000000000000000000 : ℝ)*base73 + (71258480540393/865850000000000000000000000 : ℝ)*base74 + (612432173827919/1659950000000000000000000000 : ℝ)*base77 + (1769398066098768341/28745354150000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (7273/25000000000000000 : ℝ)*base86 + (7273/25000000000000000 : ℝ)*base88 + (7273/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10417/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10417/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2782277661915478760217239319/287992516890312500000000000000000 : ℝ) := by norm_num
    linear_combination (3042931122233/1000000000000 : ℝ)*(base39) + (1954133/500000000000 : ℝ)*(base40) + (107640977577/125000000000 : ℝ)*(base60) + (8612321966143/500000000000 : ℝ)*(major_s5_0) + (8612321966143/500000000000 : ℝ)*(major_s5_1) + (8612321966143/500000000000 : ℝ)*(major_s5_2) + (22009391/1000000000000 : ℝ)*(sp_s5_6) + (56555689/500000000000 : ℝ)*(sp_s5_7) + (2011267/15625000000 : ℝ)*(sp_s5_8) + (232778304693/10000000000 : ℝ)*(sp_s5_14) + (2327781485959/100000000000 : ℝ)*(sp_s5_15) + (23277940300937/1000000000000 : ℝ)*(sp_s5_16) + (5585659527093/500000000000 : ℝ)*(sp_s5_20) + (3279741/1000000000000 : ℝ)*(sp_s5_23) + (11171341063577/1000000000000 : ℝ)*(f.failure) + (11638971790339/500000000000 : ℝ)*(f.sum) + (3053297960441651/69397877500000000000000000000 : ℝ)*base63 + (6592157429999/10018750000000000000000000 : ℝ)*base64 + (232587677011673/865850000000000000000000000 : ℝ)*base67 + (9391315427943/80150000000000000000000000 : ℝ)*base68 + (430897235054647469/665224962500000000000000000000 : ℝ)*base70 + (500380565650981/829975000000000000000000000 : ℝ)*base73 + (331742177978943/865850000000000000000000000 : ℝ)*base74 + (901336166057221/1659950000000000000000000000 : ℝ)*base76 + (6517078392151861943/14372677075000000000000000000000 : ℝ)*base79 + (41661/50000000000000000 : ℝ)*base87 + (41661/50000000000000000 : ℝ)*base89 + (41661/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-82/625 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-82/625 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (545236158349372020192590395449/64510323783430000000000000000000000 : ℝ) := by norm_num
    linear_combination (450007155563/200000000000 : ℝ)*(base39) + (931417/250000000000 : ℝ)*(base50) + (189620064613/1000000000000 : ℝ)*(base60) + (10741814266787/1000000000000 : ℝ)*(major_s5_0) + (10741814266787/1000000000000 : ℝ)*(major_s5_1) + (10741814266787/1000000000000 : ℝ)*(major_s5_2) + (61945719/1000000000000 : ℝ)*(sp_s5_1) + (279290903/1000000000000 : ℝ)*(sp_s5_2) + (59530981/500000000000 : ℝ)*(sp_s5_13) + (9798561/40000000000 : ℝ)*(sp_s5_20) + (7258418040577/500000000000 : ℝ)*(sp_s5_21) + (2903354827087/200000000000 : ℝ)*(sp_s5_22) + (14516556790251/1000000000000 : ℝ)*(sp_s5_23) + (43540160057/6250000000 : ℝ)*(sp_s5_27) + (1741697408777/250000000000 : ℝ)*(f.failure) + (7258418040577/500000000000 : ℝ)*(f.sum) + (237495980289439469/388628114000000000000000000000 : ℝ)*base63 + (249317670929009/1122100000000000000000000000 : ℝ)*base65 + (238991813263273/1731700000000000000000000000 : ℝ)*base66 + (692529655421111/1122100000000000000000000000 : ℝ)*base69 + (1927060845195788007/37252597900000000000000000000000 : ℝ)*base71 + (47679102578723/207493750000000000000000000 : ℝ)*base73 + (961010203846583/1731700000000000000000000000 : ℝ)*base75 + (176483096174977/414987500000000000000000000 : ℝ)*base77 + (30986564343353177749/57490708300000000000000000000000 : ℝ)*base79 + (7761/12500000000000000 : ℝ)*base87 + (7761/12500000000000000 : ℝ)*base89 + (7761/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev4 : (0 : ℝ) ≤ ((33199/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33199/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17317/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17317/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11221/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11221/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((19751/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19751/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10417/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10417/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-82/625 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-82/625 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306054_s5 p hpa hpb X hX hprev4

#print axioms solution

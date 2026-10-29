-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310061_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:28:04.037745+00:00
-- url     : https://prove2.me/submissions/dcaa737f-b0e7-476e-9c3e-bc1bd8dec6a5

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
theorem collision_support_c310061_s2_s2_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1713501949/10000000000 : ℝ)*x 0 + (576024949/1250000000 : ℝ)*x 1 + (6111621997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1713501949/10000000000 : ℝ)^71 ≤ (10256865698993/100000000000000 : ℝ)^55 := by
    have hnat : (1713501949 : ℕ)^71*100000000000000^55 ≤ 10256865698993^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713501949 10000000000 10256865698993 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (576024949/1250000000 : ℝ)^71 ≤ (4597899613441/12500000000000 : ℝ)^55 := by
    have hnat : (576024949 : ℕ)^71*12500000000000^55 ≤ 4597899613441^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576024949 1250000000 4597899613441 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6111621997/10000000000 : ℝ)^71 ≤ (13239984344281/25000000000000 : ℝ)^55 := by
    have hnat : (6111621997 : ℕ)^71*25000000000000^55 ≤ 13239984344281^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6111621997 10000000000 13239984344281 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1713501949/10000000000 : ℝ), (576024949/1250000000 : ℝ), (6111621997/10000000000 : ℝ)] ![(10256865698993/100000000000000 : ℝ), (4597899613441/12500000000000 : ℝ), (13239984344281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1713501949/10000000000 : ℝ)|^71 ≤ (10256865698993/100000000000000 : ℝ)^55
        have hw : |(-1713501949/10000000000 : ℝ)|=(1713501949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(576024949/1250000000 : ℝ)|^71 ≤ (4597899613441/12500000000000 : ℝ)^55
        have hw : |(576024949/1250000000 : ℝ)|=(576024949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6111621997/10000000000 : ℝ)|^71 ≤ (13239984344281/25000000000000 : ℝ)^55
        have hw : |(6111621997/10000000000 : ℝ)|=(6111621997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s2_s2_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4750426643/10000000000 : ℝ)*x 0 + (-864744879/5000000000 : ℝ)*x 1 + (5968477193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4750426643/10000000000 : ℝ)^71 ≤ (9563815820421/25000000000000 : ℝ)^55 := by
    have hnat : (4750426643 : ℕ)^71*25000000000000^55 ≤ 9563815820421^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4750426643 10000000000 9563815820421 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (864744879/5000000000 : ℝ)^71 ≤ (10380575011131/100000000000000 : ℝ)^55 := by
    have hnat : (864744879 : ℕ)^71*100000000000000^55 ≤ 10380575011131^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864744879 5000000000 10380575011131 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5968477193/10000000000 : ℝ)^71 ≤ (51364161693209/100000000000000 : ℝ)^55 := by
    have hnat : (5968477193 : ℕ)^71*100000000000000^55 ≤ 51364161693209^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5968477193 10000000000 51364161693209 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4750426643/10000000000 : ℝ), (-864744879/5000000000 : ℝ), (5968477193/10000000000 : ℝ)] ![(9563815820421/25000000000000 : ℝ), (10380575011131/100000000000000 : ℝ), (51364161693209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4750426643/10000000000 : ℝ)|^71 ≤ (9563815820421/25000000000000 : ℝ)^55
        have hw : |(4750426643/10000000000 : ℝ)|=(4750426643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-864744879/5000000000 : ℝ)|^71 ≤ (10380575011131/100000000000000 : ℝ)^55
        have hw : |(-864744879/5000000000 : ℝ)|=(864744879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5968477193/10000000000 : ℝ)|^71 ≤ (51364161693209/100000000000000 : ℝ)^55
        have hw : |(5968477193/10000000000 : ℝ)|=(5968477193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s2_s2_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6461635491/10000000000 : ℝ)*x 0 + (2773909403/10000000000 : ℝ)*x 1 + (413672489/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6461635491/10000000000 : ℝ)^71 ≤ (1778358737399/3125000000000 : ℝ)^55 := by
    have hnat : (6461635491 : ℕ)^71*3125000000000^55 ≤ 1778358737399^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6461635491 10000000000 1778358737399 3125000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2773909403/10000000000 : ℝ)^71 ≤ (3820434407489/20000000000000 : ℝ)^55 := by
    have hnat : (2773909403 : ℕ)^71*20000000000000^55 ≤ 3820434407489^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2773909403 10000000000 3820434407489 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413672489/1250000000 : ℝ)^71 ≤ (23990348345719/100000000000000 : ℝ)^55 := by
    have hnat : (413672489 : ℕ)^71*100000000000000^55 ≤ 23990348345719^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413672489 1250000000 23990348345719 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6461635491/10000000000 : ℝ), (2773909403/10000000000 : ℝ), (413672489/1250000000 : ℝ)] ![(1778358737399/3125000000000 : ℝ), (3820434407489/20000000000000 : ℝ), (23990348345719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6461635491/10000000000 : ℝ)|^71 ≤ (1778358737399/3125000000000 : ℝ)^55
        have hw : |(6461635491/10000000000 : ℝ)|=(6461635491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2773909403/10000000000 : ℝ)|^71 ≤ (3820434407489/20000000000000 : ℝ)^55
        have hw : |(2773909403/10000000000 : ℝ)|=(2773909403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(413672489/1250000000 : ℝ)|^71 ≤ (23990348345719/100000000000000 : ℝ)^55
        have hw : |(413672489/1250000000 : ℝ)|=(413672489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s2_s2_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1744863429/10000000000 : ℝ)*x 0 + (3419208567/10000000000 : ℝ)*x 1 + (88974669/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1744863429/10000000000 : ℝ)^71 ≤ (10499846502531/100000000000000 : ℝ)^55 := by
    have hnat : (1744863429 : ℕ)^71*100000000000000^55 ≤ 10499846502531^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744863429 10000000000 10499846502531 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3419208567/10000000000 : ℝ)^71 ≤ (12511526936479/50000000000000 : ℝ)^55 := by
    have hnat : (3419208567 : ℕ)^71*50000000000000^55 ≤ 12511526936479^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3419208567 10000000000 12511526936479 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88974669/125000000 : ℝ)^71 ≤ (64477099612087/100000000000000 : ℝ)^55 := by
    have hnat : (88974669 : ℕ)^71*100000000000000^55 ≤ 64477099612087^55*125000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88974669 125000000 64477099612087 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1744863429/10000000000 : ℝ), (3419208567/10000000000 : ℝ), (88974669/125000000 : ℝ)] ![(10499846502531/100000000000000 : ℝ), (12511526936479/50000000000000 : ℝ), (64477099612087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1744863429/10000000000 : ℝ)|^71 ≤ (10499846502531/100000000000000 : ℝ)^55
        have hw : |(-1744863429/10000000000 : ℝ)|=(1744863429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3419208567/10000000000 : ℝ)|^71 ≤ (12511526936479/50000000000000 : ℝ)^55
        have hw : |(3419208567/10000000000 : ℝ)|=(3419208567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(88974669/125000000 : ℝ)|^71 ≤ (64477099612087/100000000000000 : ℝ)^55
        have hw : |(88974669/125000000 : ℝ)|=(88974669/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s2_s2_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3840038291/10000000000 : ℝ)*x 0 + (-302266923/2500000000 : ℝ)*x 1 + (7110761021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3840038291/10000000000 : ℝ)^71 ≤ (2906798913119/10000000000000 : ℝ)^55 := by
    have hnat : (3840038291 : ℕ)^71*10000000000000^55 ≤ 2906798913119^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3840038291 10000000000 2906798913119 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (302266923/2500000000 : ℝ)^71 ≤ (6539238229007/100000000000000 : ℝ)^55 := by
    have hnat : (302266923 : ℕ)^71*100000000000000^55 ≤ 6539238229007^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302266923 2500000000 6539238229007 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7110761021/10000000000 : ℝ)^71 ≤ (64392772637109/100000000000000 : ℝ)^55 := by
    have hnat : (7110761021 : ℕ)^71*100000000000000^55 ≤ 64392772637109^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7110761021 10000000000 64392772637109 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3840038291/10000000000 : ℝ), (-302266923/2500000000 : ℝ), (7110761021/10000000000 : ℝ)] ![(2906798913119/10000000000000 : ℝ), (6539238229007/100000000000000 : ℝ), (64392772637109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3840038291/10000000000 : ℝ)|^71 ≤ (2906798913119/10000000000000 : ℝ)^55
        have hw : |(3840038291/10000000000 : ℝ)|=(3840038291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-302266923/2500000000 : ℝ)|^71 ≤ (6539238229007/100000000000000 : ℝ)^55
        have hw : |(-302266923/2500000000 : ℝ)|=(302266923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7110761021/10000000000 : ℝ)|^71 ≤ (64392772637109/100000000000000 : ℝ)^55
        have hw : |(7110761021/10000000000 : ℝ)|=(7110761021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s2_s2_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3935436837/10000000000 : ℝ)*x 0 + (1517102389/2000000000 : ℝ)*x 1 + (-13213/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3935436837/10000000000 : ℝ)^71 ≤ (15001777400439/50000000000000 : ℝ)^55 := by
    have hnat : (3935436837 : ℕ)^71*50000000000000^55 ≤ 15001777400439^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3935436837 10000000000 15001777400439 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1517102389/2000000000 : ℝ)^71 ≤ (69995708194021/100000000000000 : ℝ)^55 := by
    have hnat : (1517102389 : ℕ)^71*100000000000000^55 ≤ 69995708194021^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517102389 2000000000 69995708194021 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13213/125000000 : ℝ)^71 ≤ (368496593/50000000000000 : ℝ)^55 := by
    have hnat : (13213 : ℕ)^71*50000000000000^55 ≤ 368496593^55*125000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13213 125000000 368496593 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3935436837/10000000000 : ℝ), (1517102389/2000000000 : ℝ), (-13213/125000000 : ℝ)] ![(15001777400439/50000000000000 : ℝ), (69995708194021/100000000000000 : ℝ), (368496593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3935436837/10000000000 : ℝ)|^71 ≤ (15001777400439/50000000000000 : ℝ)^55
        have hw : |(3935436837/10000000000 : ℝ)|=(3935436837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1517102389/2000000000 : ℝ)|^71 ≤ (69995708194021/100000000000000 : ℝ)^55
        have hw : |(1517102389/2000000000 : ℝ)|=(1517102389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13213/125000000 : ℝ)|^71 ≤ (368496593/50000000000000 : ℝ)^55
        have hw : |(-13213/125000000 : ℝ)|=(13213/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s2_s2_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2596332943/5000000000 : ℝ)*x 0 + (5436167687/10000000000 : ℝ)*x 1 + (469883157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596332943/5000000000 : ℝ)^71 ≤ (42913590585429/100000000000000 : ℝ)^55 := by
    have hnat : (2596332943 : ℕ)^71*100000000000000^55 ≤ 42913590585429^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596332943 5000000000 42913590585429 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436167687/10000000000 : ℝ)^71 ≤ (45528896769977/100000000000000 : ℝ)^55 := by
    have hnat : (5436167687 : ℕ)^71*100000000000000^55 ≤ 45528896769977^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436167687 10000000000 45528896769977 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (469883157/2500000000 : ℝ)^71 ≤ (11557512631029/100000000000000 : ℝ)^55 := by
    have hnat : (469883157 : ℕ)^71*100000000000000^55 ≤ 11557512631029^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469883157 2500000000 11557512631029 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596332943/5000000000 : ℝ), (5436167687/10000000000 : ℝ), (469883157/2500000000 : ℝ)] ![(42913590585429/100000000000000 : ℝ), (45528896769977/100000000000000 : ℝ), (11557512631029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596332943/5000000000 : ℝ)|^71 ≤ (42913590585429/100000000000000 : ℝ)^55
        have hw : |(2596332943/5000000000 : ℝ)|=(2596332943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436167687/10000000000 : ℝ)|^71 ≤ (45528896769977/100000000000000 : ℝ)^55
        have hw : |(5436167687/10000000000 : ℝ)|=(5436167687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(469883157/2500000000 : ℝ)|^71 ≤ (11557512631029/100000000000000 : ℝ)^55
        have hw : |(469883157/2500000000 : ℝ)|=(469883157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s2_s2_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-182130221/2500000000 : ℝ)*x 0 + (92929671/250000000 : ℝ)*x 1 + (7478749393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182130221/2500000000 : ℝ)^71 ≤ (3400290671413/100000000000000 : ℝ)^55 := by
    have hnat : (182130221 : ℕ)^71*100000000000000^55 ≤ 3400290671413^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182130221 2500000000 3400290671413 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92929671/250000000 : ℝ)^71 ≤ (6968284261431/25000000000000 : ℝ)^55 := by
    have hnat : (92929671 : ℕ)^71*25000000000000^55 ≤ 6968284261431^55*250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92929671 250000000 6968284261431 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7478749393/10000000000 : ℝ)^71 ≤ (17181643067019/25000000000000 : ℝ)^55 := by
    have hnat : (7478749393 : ℕ)^71*25000000000000^55 ≤ 17181643067019^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7478749393 10000000000 17181643067019 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-182130221/2500000000 : ℝ), (92929671/250000000 : ℝ), (7478749393/10000000000 : ℝ)] ![(3400290671413/100000000000000 : ℝ), (6968284261431/25000000000000 : ℝ), (17181643067019/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-182130221/2500000000 : ℝ)|^71 ≤ (3400290671413/100000000000000 : ℝ)^55
        have hw : |(-182130221/2500000000 : ℝ)|=(182130221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(92929671/250000000 : ℝ)|^71 ≤ (6968284261431/25000000000000 : ℝ)^55
        have hw : |(92929671/250000000 : ℝ)|=(92929671/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7478749393/10000000000 : ℝ)|^71 ≤ (17181643067019/25000000000000 : ℝ)^55
        have hw : |(7478749393/10000000000 : ℝ)|=(7478749393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s2_s2_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (796573721/2500000000 : ℝ)*x 0 + (-370990299/2500000000 : ℝ)*x 1 + (3735570769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (796573721/2500000000 : ℝ)^71 ≤ (11422399420447/50000000000000 : ℝ)^55 := by
    have hnat : (796573721 : ℕ)^71*50000000000000^55 ≤ 11422399420447^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796573721 2500000000 11422399420447 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (370990299/2500000000 : ℝ)^71 ≤ (8518866854563/100000000000000 : ℝ)^55 := by
    have hnat : (370990299 : ℕ)^71*100000000000000^55 ≤ 8518866854563^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370990299 2500000000 8518866854563 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3735570769/5000000000 : ℝ)^71 ≤ (68636334299801/100000000000000 : ℝ)^55 := by
    have hnat : (3735570769 : ℕ)^71*100000000000000^55 ≤ 68636334299801^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3735570769 5000000000 68636334299801 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(796573721/2500000000 : ℝ), (-370990299/2500000000 : ℝ), (3735570769/5000000000 : ℝ)] ![(11422399420447/50000000000000 : ℝ), (8518866854563/100000000000000 : ℝ), (68636334299801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(796573721/2500000000 : ℝ)|^71 ≤ (11422399420447/50000000000000 : ℝ)^55
        have hw : |(796573721/2500000000 : ℝ)|=(796573721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-370990299/2500000000 : ℝ)|^71 ≤ (8518866854563/100000000000000 : ℝ)^55
        have hw : |(-370990299/2500000000 : ℝ)|=(370990299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3735570769/5000000000 : ℝ)|^71 ≤ (68636334299801/100000000000000 : ℝ)^55
        have hw : |(3735570769/5000000000 : ℝ)|=(3735570769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s2_s2_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6756330793/10000000000 : ℝ)*x 0 + (1221344299/2500000000 : ℝ)*x 1 + (-30355483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6756330793/10000000000 : ℝ)^71 ≤ (7534982912323/12500000000000 : ℝ)^55 := by
    have hnat : (6756330793 : ℕ)^71*12500000000000^55 ≤ 7534982912323^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6756330793 10000000000 7534982912323 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1221344299/2500000000 : ℝ)^71 ≤ (19831964417703/50000000000000 : ℝ)^55 := by
    have hnat : (1221344299 : ℕ)^71*50000000000000^55 ≤ 19831964417703^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221344299 2500000000 19831964417703 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30355483/10000000000 : ℝ)^71 ≤ (56207859257/100000000000000 : ℝ)^55 := by
    have hnat : (30355483 : ℕ)^71*100000000000000^55 ≤ 56207859257^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30355483 10000000000 56207859257 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6756330793/10000000000 : ℝ), (1221344299/2500000000 : ℝ), (-30355483/10000000000 : ℝ)] ![(7534982912323/12500000000000 : ℝ), (19831964417703/50000000000000 : ℝ), (56207859257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6756330793/10000000000 : ℝ)|^71 ≤ (7534982912323/12500000000000 : ℝ)^55
        have hw : |(6756330793/10000000000 : ℝ)|=(6756330793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1221344299/2500000000 : ℝ)|^71 ≤ (19831964417703/50000000000000 : ℝ)^55
        have hw : |(1221344299/2500000000 : ℝ)|=(1221344299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30355483/10000000000 : ℝ)|^71 ≤ (56207859257/100000000000000 : ℝ)^55
        have hw : |(-30355483/10000000000 : ℝ)|=(30355483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s2_s2_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7931595913/10000000000 : ℝ)*x 0 + (2406370031/10000000000 : ℝ)*x 1 + (52321113/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7931595913/10000000000 : ℝ)^71 ≤ (74145305378357/100000000000000 : ℝ)^55 := by
    have hnat : (7931595913 : ℕ)^71*100000000000000^55 ≤ 74145305378357^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7931595913 10000000000 74145305378357 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2406370031/10000000000 : ℝ)^71 ≤ (7949963152233/50000000000000 : ℝ)^55 := by
    have hnat : (2406370031 : ℕ)^71*50000000000000^55 ≤ 7949963152233^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406370031 10000000000 7949963152233 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52321113/312500000 : ℝ)^71 ≤ (9954768309009/100000000000000 : ℝ)^55 := by
    have hnat : (52321113 : ℕ)^71*100000000000000^55 ≤ 9954768309009^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52321113 312500000 9954768309009 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7931595913/10000000000 : ℝ), (2406370031/10000000000 : ℝ), (52321113/312500000 : ℝ)] ![(74145305378357/100000000000000 : ℝ), (7949963152233/50000000000000 : ℝ), (9954768309009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7931595913/10000000000 : ℝ)|^71 ≤ (74145305378357/100000000000000 : ℝ)^55
        have hw : |(7931595913/10000000000 : ℝ)|=(7931595913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2406370031/10000000000 : ℝ)|^71 ≤ (7949963152233/50000000000000 : ℝ)^55
        have hw : |(2406370031/10000000000 : ℝ)|=(2406370031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52321113/312500000 : ℝ)|^71 ≤ (9954768309009/100000000000000 : ℝ)^55
        have hw : |(52321113/312500000 : ℝ)|=(52321113/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s2_s2_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3522931/78125000 : ℝ)*x 0 + (3049173203/5000000000 : ℝ)*x 1 + (1355087663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3522931/78125000 : ℝ)^71 ≤ (1830558722557/100000000000000 : ℝ)^55 := by
    have hnat : (3522931 : ℕ)^71*100000000000000^55 ≤ 1830558722557^55*78125000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3522931 78125000 1830558722557 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3049173203/5000000000 : ℝ)^71 ≤ (2640573975937/5000000000000 : ℝ)^55 := by
    have hnat : (3049173203 : ℕ)^71*5000000000000^55 ≤ 2640573975937^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3049173203 5000000000 2640573975937 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355087663/2500000000 : ℝ)^71 ≤ (45357961747997/100000000000000 : ℝ)^55 := by
    have hnat : (1355087663 : ℕ)^71*100000000000000^55 ≤ 45357961747997^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355087663 2500000000 45357961747997 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3522931/78125000 : ℝ), (3049173203/5000000000 : ℝ), (1355087663/2500000000 : ℝ)] ![(1830558722557/100000000000000 : ℝ), (2640573975937/5000000000000 : ℝ), (45357961747997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3522931/78125000 : ℝ)|^71 ≤ (1830558722557/100000000000000 : ℝ)^55
        have hw : |(-3522931/78125000 : ℝ)|=(3522931/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3049173203/5000000000 : ℝ)|^71 ≤ (2640573975937/5000000000000 : ℝ)^55
        have hw : |(3049173203/5000000000 : ℝ)|=(3049173203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355087663/2500000000 : ℝ)|^71 ≤ (45357961747997/100000000000000 : ℝ)^55
        have hw : |(1355087663/2500000000 : ℝ)|=(1355087663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s2_s2_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3296465951/5000000000 : ℝ)*x 0 + (-55337569/1250000000 : ℝ)*x 1 + (612388519/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3296465951/5000000000 : ℝ)^71 ≤ (58404580251873/100000000000000 : ℝ)^55 := by
    have hnat : (3296465951 : ℕ)^71*100000000000000^55 ≤ 58404580251873^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3296465951 5000000000 58404580251873 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55337569/1250000000 : ℝ)^71 ≤ (357504216657/20000000000000 : ℝ)^55 := by
    have hnat : (55337569 : ℕ)^71*20000000000000^55 ≤ 357504216657^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55337569 1250000000 357504216657 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (612388519/1250000000 : ℝ)^71 ≤ (9951974663497/25000000000000 : ℝ)^55 := by
    have hnat : (612388519 : ℕ)^71*25000000000000^55 ≤ 9951974663497^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612388519 1250000000 9951974663497 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3296465951/5000000000 : ℝ), (-55337569/1250000000 : ℝ), (612388519/1250000000 : ℝ)] ![(58404580251873/100000000000000 : ℝ), (357504216657/20000000000000 : ℝ), (9951974663497/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3296465951/5000000000 : ℝ)|^71 ≤ (58404580251873/100000000000000 : ℝ)^55
        have hw : |(3296465951/5000000000 : ℝ)|=(3296465951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55337569/1250000000 : ℝ)|^71 ≤ (357504216657/20000000000000 : ℝ)^55
        have hw : |(-55337569/1250000000 : ℝ)|=(55337569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(612388519/1250000000 : ℝ)|^71 ≤ (9951974663497/25000000000000 : ℝ)^55
        have hw : |(612388519/1250000000 : ℝ)|=(612388519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s2_s2_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (860197321/2500000000 : ℝ)*x 0 + (12582083/16000000 : ℝ)*x 1 + (-11730503/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860197321/2500000000 : ℝ)^71 ≤ (5045424305829/20000000000000 : ℝ)^55 := by
    have hnat : (860197321 : ℕ)^71*20000000000000^55 ≤ 5045424305829^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860197321 2500000000 5045424305829 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12582083/16000000 : ℝ)^71 ≤ (73328217305329/100000000000000 : ℝ)^55 := by
    have hnat : (12582083 : ℕ)^71*100000000000000^55 ≤ 73328217305329^55*16000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12582083 16000000 73328217305329 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11730503/312500000 : ℝ)^71 ≤ (722330571317/50000000000000 : ℝ)^55 := by
    have hnat : (11730503 : ℕ)^71*50000000000000^55 ≤ 722330571317^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11730503 312500000 722330571317 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860197321/2500000000 : ℝ), (12582083/16000000 : ℝ), (-11730503/312500000 : ℝ)] ![(5045424305829/20000000000000 : ℝ), (73328217305329/100000000000000 : ℝ), (722330571317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860197321/2500000000 : ℝ)|^71 ≤ (5045424305829/20000000000000 : ℝ)^55
        have hw : |(860197321/2500000000 : ℝ)|=(860197321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12582083/16000000 : ℝ)|^71 ≤ (73328217305329/100000000000000 : ℝ)^55
        have hw : |(12582083/16000000 : ℝ)|=(12582083/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11730503/312500000 : ℝ)|^71 ≤ (722330571317/50000000000000 : ℝ)^55
        have hw : |(-11730503/312500000 : ℝ)|=(11730503/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310061_s2_s2_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8448697609/10000000000 : ℝ)*x 0 + (1696237199/10000000000 : ℝ)*x 1 + (1605834297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8448697609/10000000000 : ℝ)^71 ≤ (40221869091567/50000000000000 : ℝ)^55 := by
    have hnat : (8448697609 : ℕ)^71*50000000000000^55 ≤ 40221869091567^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8448697609 10000000000 40221869091567 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1696237199/10000000000 : ℝ)^71 ≤ (2530913103017/25000000000000 : ℝ)^55 := by
    have hnat : (1696237199 : ℕ)^71*25000000000000^55 ≤ 2530913103017^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696237199 10000000000 2530913103017 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1605834297/10000000000 : ℝ)^71 ≤ (471630469547/5000000000000 : ℝ)^55 := by
    have hnat : (1605834297 : ℕ)^71*5000000000000^55 ≤ 471630469547^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1605834297 10000000000 471630469547 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8448697609/10000000000 : ℝ), (1696237199/10000000000 : ℝ), (1605834297/10000000000 : ℝ)] ![(40221869091567/50000000000000 : ℝ), (2530913103017/25000000000000 : ℝ), (471630469547/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8448697609/10000000000 : ℝ)|^71 ≤ (40221869091567/50000000000000 : ℝ)^55
        have hw : |(8448697609/10000000000 : ℝ)|=(8448697609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1696237199/10000000000 : ℝ)|^71 ≤ (2530913103017/25000000000000 : ℝ)^55
        have hw : |(1696237199/10000000000 : ℝ)|=(1696237199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1605834297/10000000000 : ℝ)|^71 ≤ (471630469547/5000000000000 : ℝ)^55
        have hw : |(1605834297/10000000000 : ℝ)|=(1605834297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310061_s2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((38247/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38247/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4809/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4809/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36469/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36469/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((59399/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(59399/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31631/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31631/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57919/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57919/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (18111/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (38247/50000 : ℝ) ^ (35/8 : ℝ) ≤ (7741226221473789717/25000000000000000000 : ℝ) := by
    have hpowers : (38247/50000 : ℝ)^35 ≤ (7741226221473789717/25000000000000000000 : ℝ)^8 := by
      have hnat : (38247 : ℕ)^35*25000000000000000000^8 ≤ 7741226221473789717^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38247 50000 7741226221473789717 25000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38247/50000 : ℝ)) (X := (7741226221473789717/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (32741226221473789717/25000000000000000000 : ℝ) ≤ (10635998566862147/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (32741226221473789717/25000000000000000000 : ℝ)^8 ≤ (10635998566862147/10000000000000000 : ℝ)^35 := by
      have hnat : (32741226221473789717 : ℕ)^8*10000000000000000^35 ≤ 10635998566862147^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32741226221473789717 25000000000000000000 10635998566862147 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10635998566862147/10000000000000000 : ℝ)) (X := (32741226221473789717/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (20241226221473789717/12500000000000000000 : ℝ) ≤ (11164676069224859/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (20241226221473789717/12500000000000000000 : ℝ)^8 ≤ (11164676069224859/10000000000000000 : ℝ)^35 := by
      have hnat : (20241226221473789717 : ℕ)^8*10000000000000000^35 ≤ 11164676069224859^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20241226221473789717 12500000000000000000 11164676069224859 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11164676069224859/10000000000000000 : ℝ)) (X := (20241226221473789717/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(635998566862147/7649400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(22028229265113/318725000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (38247/50000 : ℝ)) (alpha := (635998566862147/7649400000000000 : ℝ)) (beta := (22028229265113/318725000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (38247/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(635998566862147/7649400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(22028229265113/318725000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (4809/6250 : ℝ) ^ (35/8 : ℝ) ≤ (7942451700618814679/25000000000000000000 : ℝ) := by
    have hpowers : (4809/6250 : ℝ)^35 ≤ (7942451700618814679/25000000000000000000 : ℝ)^8 := by
      have hnat : (4809 : ℕ)^35*25000000000000000000^8 ≤ 7942451700618814679^8*6250^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4809 6250 7942451700618814679 25000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4809/6250 : ℝ)) (X := (7942451700618814679/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (32942451700618814679/25000000000000000000 : ℝ) ≤ (2130180914091243/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (32942451700618814679/25000000000000000000 : ℝ)^8 ≤ (2130180914091243/2000000000000000 : ℝ)^35 := by
      have hnat : (32942451700618814679 : ℕ)^8*2000000000000000^35 ≤ 2130180914091243^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32942451700618814679 25000000000000000000 2130180914091243 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2130180914091243/2000000000000000 : ℝ)) (X := (32942451700618814679/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (20442451700618814679/12500000000000000000 : ℝ) ≤ (559497449546571/500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (20442451700618814679/12500000000000000000 : ℝ)^8 ≤ (559497449546571/500000000000000 : ℝ)^35 := by
      have hnat : (20442451700618814679 : ℕ)^8*500000000000000^35 ≤ 559497449546571^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20442451700618814679 12500000000000000000 559497449546571 500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (559497449546571/500000000000000 : ℝ)) (X := (20442451700618814679/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(130180914091243/1538880000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(35936294698347/512960000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (4809/6250 : ℝ)) (alpha := (130180914091243/1538880000000000 : ℝ)) (beta := (35936294698347/512960000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (4809/6250 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(130180914091243/1538880000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(35936294698347/512960000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (36469/50000 : ℝ) ^ (35/8 : ℝ) ≤ (25143347410476691407/100000000000000000000 : ℝ) := by
    have hpowers : (36469/50000 : ℝ)^35 ≤ (25143347410476691407/100000000000000000000 : ℝ)^8 := by
      have hnat : (36469 : ℕ)^35*100000000000000000000^8 ≤ 25143347410476691407^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36469 50000 25143347410476691407 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36469/50000 : ℝ)) (X := (25143347410476691407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (125143347410476691407/100000000000000000000 : ℝ) ≤ (10526030706064199/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (125143347410476691407/100000000000000000000 : ℝ)^8 ≤ (10526030706064199/10000000000000000 : ℝ)^35 := by
      have hnat : (125143347410476691407 : ℕ)^8*10000000000000000^35 ≤ 10526030706064199^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125143347410476691407 100000000000000000000 10526030706064199 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10526030706064199/10000000000000000 : ℝ)) (X := (125143347410476691407/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (75143347410476691407/50000000000000000000 : ℝ) ≤ (10975870619445273/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (75143347410476691407/50000000000000000000 : ℝ)^8 ≤ (10975870619445273/10000000000000000 : ℝ)^35 := by
      have hnat : (75143347410476691407 : ℕ)^8*10000000000000000^35 ≤ 10975870619445273^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75143347410476691407 50000000000000000000 10975870619445273 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10975870619445273/10000000000000000 : ℝ)) (X := (75143347410476691407/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(526030706064199/7293800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(224919956690537/3646900000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (36469/50000 : ℝ)) (alpha := (526030706064199/7293800000000000 : ℝ)) (beta := (224919956690537/3646900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (36469/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(526030706064199/7293800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(224919956690537/3646900000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1713501949/10000000000 : ℝ)*X 0 0+(576024949/1250000000 : ℝ)*X 0 1+(6111621997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((4750426643/10000000000 : ℝ)*X 1 0+(-864744879/5000000000 : ℝ)*X 1 1+(5968477193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((6461635491/10000000000 : ℝ)*X 0 0+(2773909403/10000000000 : ℝ)*X 0 1+(413672489/1250000000 : ℝ)*X 0 2+(6461635491/10000000000 : ℝ)*X 1 0+(2773909403/10000000000 : ℝ)*X 1 1+(413672489/1250000000 : ℝ)*X 1 2+(6461635491/10000000000 : ℝ)*X 2 0+(2773909403/10000000000 : ℝ)*X 2 1+(413672489/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1744863429/10000000000 : ℝ)*X 0 0+(3419208567/10000000000 : ℝ)*X 0 1+(88974669/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((3840038291/10000000000 : ℝ)*X 1 0+(-302266923/2500000000 : ℝ)*X 1 1+(7110761021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((3935436837/10000000000 : ℝ)*X 2 0+(1517102389/2000000000 : ℝ)*X 2 1+(-13213/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((2596332943/5000000000 : ℝ)*X 0 0+(5436167687/10000000000 : ℝ)*X 0 1+(469883157/2500000000 : ℝ)*X 0 2+(2596332943/5000000000 : ℝ)*X 1 0+(5436167687/10000000000 : ℝ)*X 1 1+(469883157/2500000000 : ℝ)*X 1 2+(2596332943/5000000000 : ℝ)*X 2 0+(5436167687/10000000000 : ℝ)*X 2 1+(469883157/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-182130221/2500000000 : ℝ)*X 0 0+(92929671/250000000 : ℝ)*X 0 1+(7478749393/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((796573721/2500000000 : ℝ)*X 1 0+(-370990299/2500000000 : ℝ)*X 1 1+(3735570769/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6756330793/10000000000 : ℝ)*X 2 0+(1221344299/2500000000 : ℝ)*X 2 1+(-30355483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((7931595913/10000000000 : ℝ)*X 0 0+(2406370031/10000000000 : ℝ)*X 0 1+(52321113/312500000 : ℝ)*X 0 2+(7931595913/10000000000 : ℝ)*X 1 0+(2406370031/10000000000 : ℝ)*X 1 1+(52321113/312500000 : ℝ)*X 1 2+(7931595913/10000000000 : ℝ)*X 2 0+(2406370031/10000000000 : ℝ)*X 2 1+(52321113/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-3522931/78125000 : ℝ)*X 0 0+(3049173203/5000000000 : ℝ)*X 0 1+(1355087663/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3296465951/5000000000 : ℝ)*X 1 0+(-55337569/1250000000 : ℝ)*X 1 1+(612388519/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((860197321/2500000000 : ℝ)*X 2 0+(12582083/16000000 : ℝ)*X 2 1+(-11730503/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((8448697609/10000000000 : ℝ)*X 0 0+(1696237199/10000000000 : ℝ)*X 0 1+(1605834297/10000000000 : ℝ)*X 0 2+(8448697609/10000000000 : ℝ)*X 1 0+(1696237199/10000000000 : ℝ)*X 1 1+(1605834297/10000000000 : ℝ)*X 1 2+(8448697609/10000000000 : ℝ)*X 2 0+(1696237199/10000000000 : ℝ)*X 2 1+(1605834297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310061_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((59399/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(59399/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5132859818416923/500000000000000000000 : ℝ) := by norm_num
    linear_combination (395017313467/1000000000000 : ℝ)*(base7) + (427787/500000000000 : ℝ)*(base50) + (283345517249/1000000000000 : ℝ)*(base59) + (1604309515669/500000000000 : ℝ)*(major_s2_0) + (1604309515669/500000000000 : ℝ)*(major_s2_1) + (1604309515669/500000000000 : ℝ)*(major_s2_2) + (17111967/1000000000000 : ℝ)*(sp_s2_0) + (1323913/500000000000 : ℝ)*(sp_s2_6) + (2097772092537/500000000000 : ℝ)*(sp_s2_7) + (1048896766337/250000000000 : ℝ)*(sp_s2_8) + (419559961523/100000000000 : ℝ)*(sp_s2_9) + (594544434759/250000000000 : ℝ)*(sp_s2_13) + (3831819/100000000000 : ℝ)*(sp_s2_14) + (6274941/500000000000 : ℝ)*(sp_s2_15) + (396632614679/200000000000 : ℝ)*(f.failure) + (419559961523/100000000000 : ℝ)*(f.sum) + (2020364347809078401/20043362400000000000000000000000 : ℝ)*base63 + (690560686301293/1823450000000000000000000000 : ℝ)*base64 + (24348910490767/36640000000000000000000000 : ℝ)*base66 + (569083643786289/3646900000000000000000000000 : ℝ)*base68 + (2523253679875748257/5579319372000000000000000000000 : ℝ)*base71 + (54484223880973/159362500000000000000000000 : ℝ)*base72 + (55419432726143/109920000000000000000000000 : ℝ)*base74 + (835513138419857/3824700000000000000000000000 : ℝ)*base76 + (1100930832752161537/2335616800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (553/20000000000000000 : ℝ)*base86 + (553/20000000000000000 : ℝ)*base88 + (553/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31631/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31631/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5765917836386482410729127/381101050000000000000000000000 : ℝ) := by norm_num
    linear_combination (68481107661/125000000000 : ℝ)*(base7) + (398311/250000000000 : ℝ)*(base40) + (3548203/250000000000 : ℝ)*(base53) + (5230433/1000000000000 : ℝ)*(base59) + (9082316047/3906250000 : ℝ)*(major_s2_0) + (9082316047/3906250000 : ℝ)*(major_s2_1) + (116252935761/50000000000 : ℝ)*(major_s2_2) + (28496243/1000000000000 : ℝ)*(sp_s2_7) + (36534703/500000000000 : ℝ)*(sp_s2_8) + (115291811381/40000000000 : ℝ)*(sp_s2_14) + (1441125355681/500000000000 : ℝ)*(sp_s2_15) + (144116898679/50000000000 : ℝ)*(sp_s2_16) + (496209519589/250000000000 : ℝ)*(sp_s2_20) + (241327/3125000000 : ℝ)*(sp_s2_27) + (1437066441707/1000000000000 : ℝ)*(f.failure) + (144116898679/50000000000 : ℝ)*(f.sum) + (29963859776458637/125271015000000000000000000000 : ℝ)*base62 + (2168574864673/364690000000000000000000000 : ℝ)*base65 + (621640253527/2290000000000000000000000 : ℝ)*base67 + (16745071437641/364690000000000000000000000 : ℝ)*base69 + (18564857622544967/571651575000000000000000000000 : ℝ)*base71 + (12217590951/5225000000000000000000000 : ℝ)*base73 + (28013276311/858750000000000000000000 : ℝ)*base75 + (4605452936239/7837500000000000000000000 : ℝ)*base77 + (171554123517353/598262500000000000000000000 : ℝ)*base78 + (99349/100000000000000000 : ℝ)*base86 + (99349/100000000000000000 : ℝ)*base88 + (99349/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57919/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57919/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4405671974470602382398489562863/298121631777200000000000000000000000 : ℝ) := by norm_num
    linear_combination (64627498367/200000000000 : ℝ)*(base7) + (8716837/1000000000000 : ℝ)*(base11) + (9889796699/62500000000 : ℝ)*(base40) + (42213776289/1000000000000 : ℝ)*(base59) + (2369017825253/1000000000000 : ℝ)*(major_s2_0) + (2369017825253/1000000000000 : ℝ)*(major_s2_1) + (2369017825253/1000000000000 : ℝ)*(major_s2_2) + (4402353/1000000000000 : ℝ)*(sp_s2_1) + (36886761/200000000000 : ℝ)*(sp_s2_9) + (7018569/1000000000000 : ℝ)*(sp_s2_20) + (192419766501/62500000000 : ℝ)*(sp_s2_21) + (6157441157/2000000000 : ℝ)*(sp_s2_22) + (384817568381/125000000000 : ℝ)*(sp_s2_23) + (1787358113061/1000000000000 : ℝ)*(sp_s2_27) + (292845527959/200000000000 : ℝ)*(f.failure) + (3078724980853/1000000000000 : ℝ)*(f.sum) + (13951191896692681159/280607073600000000000000000000000 : ℝ)*base63 + (1872616439624079/3646900000000000000000000000 : ℝ)*base65 + (65759202841897/512960000000000000000000000 : ℝ)*base66 + (224821992705153/7293800000000000000000000000 : ℝ)*base68 + (43441056404178489361/55793193720000000000000000000000 : ℝ)*base71 + (55072715824143/159362500000000000000000000 : ℝ)*base72 + (939187784107/307776000000000000000000000 : ℝ)*base75 + (2831143625253371/7649400000000000000000000000 : ℝ)*base77 + (11905232262879836777/32698635200000000000000000000000 : ℝ)*base78 + (10487/20000000000000000 : ℝ)*base87 + (10487/20000000000000000 : ℝ)*base89 + (10487/20000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((38247/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38247/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4809/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4809/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36469/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36469/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((59399/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(59399/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31631/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31631/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57919/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57919/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310061_s2 p hpa hpb X hX hprev1

#print axioms solution

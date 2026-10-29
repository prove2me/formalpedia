-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306086_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:01:01.838268+00:00
-- url     : https://prove2.me/submissions/ace5ea11-00c9-4eee-b825-05062cc6b1f4

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
theorem collision_support_c306086_s1_s1_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (408649639/625000000 : ℝ)*x 0 + (628161439/2000000000 : ℝ)*x 1 + (3016218751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408649639/625000000 : ℝ)^135 ≤ (28649149935243/50000000000000 : ℝ)^103 := by
    have hnat : (408649639 : ℕ)^135*50000000000000^103 ≤ 28649149935243^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408649639 625000000 28649149935243 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (628161439/2000000000 : ℝ)^135 ≤ (438341159523/2000000000000 : ℝ)^103 := by
    have hnat : (628161439 : ℕ)^135*2000000000000^103 ≤ 438341159523^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628161439 2000000000 438341159523 2000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3016218751/10000000000 : ℝ)^135 ≤ (20784642138227/100000000000000 : ℝ)^103 := by
    have hnat : (3016218751 : ℕ)^135*100000000000000^103 ≤ 20784642138227^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3016218751 10000000000 20784642138227 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(408649639/625000000 : ℝ), (628161439/2000000000 : ℝ), (3016218751/10000000000 : ℝ)] ![(28649149935243/50000000000000 : ℝ), (438341159523/2000000000000 : ℝ), (20784642138227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(408649639/625000000 : ℝ)|^135 ≤ (28649149935243/50000000000000 : ℝ)^103
        have hw : |(408649639/625000000 : ℝ)|=(408649639/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(628161439/2000000000 : ℝ)|^135 ≤ (438341159523/2000000000000 : ℝ)^103
        have hw : |(628161439/2000000000 : ℝ)|=(628161439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3016218751/10000000000 : ℝ)|^135 ≤ (20784642138227/100000000000000 : ℝ)^103
        have hw : |(3016218751/10000000000 : ℝ)|=(3016218751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s1_s1_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6216459283/10000000000 : ℝ)*x 0 + (-850293513/2500000000 : ℝ)*x 1 + (-788623197/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6216459283/10000000000 : ℝ)^135 ≤ (10725835636767/20000000000000 : ℝ)^103 := by
    have hnat : (6216459283 : ℕ)^135*20000000000000^103 ≤ 10725835636767^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6216459283 10000000000 10725835636767 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (850293513/2500000000 : ℝ)^135 ≤ (24328508934511/100000000000000 : ℝ)^103 := by
    have hnat : (850293513 : ℕ)^135*100000000000000^103 ≤ 24328508934511^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850293513 2500000000 24328508934511 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (788623197/2500000000 : ℝ)^135 ≤ (5510578218067/25000000000000 : ℝ)^103 := by
    have hnat : (788623197 : ℕ)^135*25000000000000^103 ≤ 5510578218067^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788623197 2500000000 5510578218067 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6216459283/10000000000 : ℝ), (-850293513/2500000000 : ℝ), (-788623197/2500000000 : ℝ)] ![(10725835636767/20000000000000 : ℝ), (24328508934511/100000000000000 : ℝ), (5510578218067/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6216459283/10000000000 : ℝ)|^135 ≤ (10725835636767/20000000000000 : ℝ)^103
        have hw : |(6216459283/10000000000 : ℝ)|=(6216459283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-850293513/2500000000 : ℝ)|^135 ≤ (24328508934511/100000000000000 : ℝ)^103
        have hw : |(-850293513/2500000000 : ℝ)|=(850293513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-788623197/2500000000 : ℝ)|^135 ≤ (5510578218067/25000000000000 : ℝ)^103
        have hw : |(-788623197/2500000000 : ℝ)|=(788623197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s1_s1_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1795395173/5000000000 : ℝ)*x 0 + (-1267757447/5000000000 : ℝ)*x 1 + (32703103/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1795395173/5000000000 : ℝ)^135 ≤ (13060706507677/50000000000000 : ℝ)^103 := by
    have hnat : (1795395173 : ℕ)^135*50000000000000^103 ≤ 13060706507677^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1795395173 5000000000 13060706507677 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1267757447/5000000000 : ℝ)^135 ≤ (4138678420201/25000000000000 : ℝ)^103 := by
    have hnat : (1267757447 : ℕ)^135*25000000000000^103 ≤ 4138678420201^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267757447 5000000000 4138678420201 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32703103/50000000 : ℝ)^135 ≤ (57323873281497/100000000000000 : ℝ)^103 := by
    have hnat : (32703103 : ℕ)^135*100000000000000^103 ≤ 57323873281497^103*50000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32703103 50000000 57323873281497 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1795395173/5000000000 : ℝ), (-1267757447/5000000000 : ℝ), (32703103/50000000 : ℝ)] ![(13060706507677/50000000000000 : ℝ), (4138678420201/25000000000000 : ℝ), (57323873281497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1795395173/5000000000 : ℝ)|^135 ≤ (13060706507677/50000000000000 : ℝ)^103
        have hw : |(1795395173/5000000000 : ℝ)|=(1795395173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1267757447/5000000000 : ℝ)|^135 ≤ (4138678420201/25000000000000 : ℝ)^103
        have hw : |(-1267757447/5000000000 : ℝ)|=(1267757447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32703103/50000000 : ℝ)|^135 ≤ (57323873281497/100000000000000 : ℝ)^103
        have hw : |(32703103/50000000 : ℝ)|=(32703103/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s1_s1_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (85614573/10000000000 : ℝ)*x 0 + (-4176417409/5000000000 : ℝ)*x 1 + (604005847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85614573/10000000000 : ℝ)^135 ≤ (39017767043/20000000000000 : ℝ)^103 := by
    have hnat : (85614573 : ℕ)^135*20000000000000^103 ≤ 39017767043^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85614573 10000000000 39017767043 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4176417409/5000000000 : ℝ)^135 ≤ (19746461644977/25000000000000 : ℝ)^103 := by
    have hnat : (4176417409 : ℕ)^135*25000000000000^103 ≤ 19746461644977^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4176417409 5000000000 19746461644977 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (604005847/2000000000 : ℝ)^135 ≤ (20819064573929/100000000000000 : ℝ)^103 := by
    have hnat : (604005847 : ℕ)^135*100000000000000^103 ≤ 20819064573929^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604005847 2000000000 20819064573929 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85614573/10000000000 : ℝ), (-4176417409/5000000000 : ℝ), (604005847/2000000000 : ℝ)] ![(39017767043/20000000000000 : ℝ), (19746461644977/25000000000000 : ℝ), (20819064573929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85614573/10000000000 : ℝ)|^135 ≤ (39017767043/20000000000000 : ℝ)^103
        have hw : |(85614573/10000000000 : ℝ)|=(85614573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4176417409/5000000000 : ℝ)|^135 ≤ (19746461644977/25000000000000 : ℝ)^103
        have hw : |(-4176417409/5000000000 : ℝ)|=(4176417409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(604005847/2000000000 : ℝ)|^135 ≤ (20819064573929/100000000000000 : ℝ)^103
        have hw : |(604005847/2000000000 : ℝ)|=(604005847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s1_s1_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3792116349/10000000000 : ℝ)*x 0 + (6518016367/10000000000 : ℝ)*x 1 + (2337145129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3792116349/10000000000 : ℝ)^135 ≤ (28057486947867/100000000000000 : ℝ)^103 := by
    have hnat : (3792116349 : ℕ)^135*100000000000000^103 ≤ 28057486947867^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3792116349 10000000000 28057486947867 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6518016367/10000000000 : ℝ)^135 ≤ (14266088521079/25000000000000 : ℝ)^103 := by
    have hnat : (6518016367 : ℕ)^135*25000000000000^103 ≤ 14266088521079^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6518016367 10000000000 14266088521079 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2337145129/10000000000 : ℝ)^135 ≤ (14878158950657/100000000000000 : ℝ)^103 := by
    have hnat : (2337145129 : ℕ)^135*100000000000000^103 ≤ 14878158950657^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2337145129 10000000000 14878158950657 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3792116349/10000000000 : ℝ), (6518016367/10000000000 : ℝ), (2337145129/10000000000 : ℝ)] ![(28057486947867/100000000000000 : ℝ), (14266088521079/25000000000000 : ℝ), (14878158950657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3792116349/10000000000 : ℝ)|^135 ≤ (28057486947867/100000000000000 : ℝ)^103
        have hw : |(3792116349/10000000000 : ℝ)|=(3792116349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6518016367/10000000000 : ℝ)|^135 ≤ (14266088521079/25000000000000 : ℝ)^103
        have hw : |(6518016367/10000000000 : ℝ)|=(6518016367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2337145129/10000000000 : ℝ)|^135 ≤ (14878158950657/100000000000000 : ℝ)^103
        have hw : |(2337145129/10000000000 : ℝ)|=(2337145129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s1_s1_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8937597963/10000000000 : ℝ)*x 0 + (-547229887/10000000000 : ℝ)*x 1 + (-239548659/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8937597963/10000000000 : ℝ)^135 ≤ (863109937239/1000000000000 : ℝ)^103 := by
    have hnat : (8937597963 : ℕ)^135*1000000000000^103 ≤ 863109937239^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8937597963 10000000000 863109937239 1000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547229887/10000000000 : ℝ)^135 ≤ (221893660431/10000000000000 : ℝ)^103 := by
    have hnat : (547229887 : ℕ)^135*10000000000000^103 ≤ 221893660431^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547229887 10000000000 221893660431 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239548659/1250000000 : ℝ)^135 ≤ (11470069652849/100000000000000 : ℝ)^103 := by
    have hnat : (239548659 : ℕ)^135*100000000000000^103 ≤ 11470069652849^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239548659 1250000000 11470069652849 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8937597963/10000000000 : ℝ), (-547229887/10000000000 : ℝ), (-239548659/1250000000 : ℝ)] ![(863109937239/1000000000000 : ℝ), (221893660431/10000000000000 : ℝ), (11470069652849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8937597963/10000000000 : ℝ)|^135 ≤ (863109937239/1000000000000 : ℝ)^103
        have hw : |(8937597963/10000000000 : ℝ)|=(8937597963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-547229887/10000000000 : ℝ)|^135 ≤ (221893660431/10000000000000 : ℝ)^103
        have hw : |(-547229887/10000000000 : ℝ)|=(547229887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-239548659/1250000000 : ℝ)|^135 ≤ (11470069652849/100000000000000 : ℝ)^103
        have hw : |(-239548659/1250000000 : ℝ)|=(239548659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s1_s1_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (450778729/1250000000 : ℝ)*x 0 + (-629504953/5000000000 : ℝ)*x 1 + (368853451/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450778729/1250000000 : ℝ)^135 ≤ (26268720797531/100000000000000 : ℝ)^103 := by
    have hnat : (450778729 : ℕ)^135*100000000000000^103 ≤ 26268720797531^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450778729 1250000000 26268720797531 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (629504953/5000000000 : ℝ)^135 ≤ (6613426817861/100000000000000 : ℝ)^103 := by
    have hnat : (629504953 : ℕ)^135*100000000000000^103 ≤ 6613426817861^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629504953 5000000000 6613426817861 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (368853451/500000000 : ℝ)^135 ≤ (8389731546737/12500000000000 : ℝ)^103 := by
    have hnat : (368853451 : ℕ)^135*12500000000000^103 ≤ 8389731546737^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368853451 500000000 8389731546737 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(450778729/1250000000 : ℝ), (-629504953/5000000000 : ℝ), (368853451/500000000 : ℝ)] ![(26268720797531/100000000000000 : ℝ), (6613426817861/100000000000000 : ℝ), (8389731546737/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(450778729/1250000000 : ℝ)|^135 ≤ (26268720797531/100000000000000 : ℝ)^103
        have hw : |(450778729/1250000000 : ℝ)|=(450778729/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-629504953/5000000000 : ℝ)|^135 ≤ (6613426817861/100000000000000 : ℝ)^103
        have hw : |(-629504953/5000000000 : ℝ)|=(629504953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(368853451/500000000 : ℝ)|^135 ≤ (8389731546737/12500000000000 : ℝ)^103
        have hw : |(368853451/500000000 : ℝ)|=(368853451/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s1_s1_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-96079/10000000000 : ℝ)*x 0 + (-400181591/1000000000 : ℝ)*x 1 + (237767399/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (96079/10000000000 : ℝ)^135 ≤ (26535877/100000000000000 : ℝ)^103 := by
    have hnat : (96079 : ℕ)^135*100000000000000^103 ≤ 26535877^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96079 10000000000 26535877 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400181591/1000000000 : ℝ)^135 ≤ (6021663662111/20000000000000 : ℝ)^103 := by
    have hnat : (400181591 : ℕ)^135*20000000000000^103 ≤ 6021663662111^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400181591 1000000000 6021663662111 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237767399/312500000 : ℝ)^135 ≤ (69891655140939/100000000000000 : ℝ)^103 := by
    have hnat : (237767399 : ℕ)^135*100000000000000^103 ≤ 69891655140939^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237767399 312500000 69891655140939 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-96079/10000000000 : ℝ), (-400181591/1000000000 : ℝ), (237767399/312500000 : ℝ)] ![(26535877/100000000000000 : ℝ), (6021663662111/20000000000000 : ℝ), (69891655140939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-96079/10000000000 : ℝ)|^135 ≤ (26535877/100000000000000 : ℝ)^103
        have hw : |(-96079/10000000000 : ℝ)|=(96079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-400181591/1000000000 : ℝ)|^135 ≤ (6021663662111/20000000000000 : ℝ)^103
        have hw : |(-400181591/1000000000 : ℝ)|=(400181591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(237767399/312500000 : ℝ)|^135 ≤ (69891655140939/100000000000000 : ℝ)^103
        have hw : |(237767399/312500000 : ℝ)|=(237767399/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s1_s1_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4358807543/5000000000 : ℝ)*x 0 + (2087404081/10000000000 : ℝ)*x 1 + (159422653/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358807543/5000000000 : ℝ)^135 ≤ (41768653113851/50000000000000 : ℝ)^103 := by
    have hnat : (4358807543 : ℕ)^135*50000000000000^103 ≤ 41768653113851^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358807543 5000000000 41768653113851 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2087404081/10000000000 : ℝ)^135 ≤ (100233334623/781250000000 : ℝ)^103 := by
    have hnat : (2087404081 : ℕ)^135*781250000000^103 ≤ 100233334623^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087404081 10000000000 100233334623 781250000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159422653/2000000000 : ℝ)^135 ≤ (908206731683/25000000000000 : ℝ)^103 := by
    have hnat : (159422653 : ℕ)^135*25000000000000^103 ≤ 908206731683^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159422653 2000000000 908206731683 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358807543/5000000000 : ℝ), (2087404081/10000000000 : ℝ), (159422653/2000000000 : ℝ)] ![(41768653113851/50000000000000 : ℝ), (100233334623/781250000000 : ℝ), (908206731683/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358807543/5000000000 : ℝ)|^135 ≤ (41768653113851/50000000000000 : ℝ)^103
        have hw : |(4358807543/5000000000 : ℝ)|=(4358807543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2087404081/10000000000 : ℝ)|^135 ≤ (100233334623/781250000000 : ℝ)^103
        have hw : |(2087404081/10000000000 : ℝ)|=(2087404081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(159422653/2000000000 : ℝ)|^135 ≤ (908206731683/25000000000000 : ℝ)^103
        have hw : |(159422653/2000000000 : ℝ)|=(159422653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s1_s1_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8198638133/10000000000 : ℝ)*x 0 + (-49970511/250000000 : ℝ)*x 1 + (-1830207109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8198638133/10000000000 : ℝ)^135 ≤ (38540117379041/50000000000000 : ℝ)^103 := by
    have hnat : (8198638133 : ℕ)^135*50000000000000^103 ≤ 38540117379041^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8198638133 10000000000 38540117379041 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49970511/250000000 : ℝ)^135 ≤ (12121000021701/100000000000000 : ℝ)^103 := by
    have hnat : (49970511 : ℕ)^135*100000000000000^103 ≤ 12121000021701^103*250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49970511 250000000 12121000021701 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1830207109/10000000000 : ℝ)^135 ≤ (1349845649833/12500000000000 : ℝ)^103 := by
    have hnat : (1830207109 : ℕ)^135*12500000000000^103 ≤ 1349845649833^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1830207109 10000000000 1349845649833 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8198638133/10000000000 : ℝ), (-49970511/250000000 : ℝ), (-1830207109/10000000000 : ℝ)] ![(38540117379041/50000000000000 : ℝ), (12121000021701/100000000000000 : ℝ), (1349845649833/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8198638133/10000000000 : ℝ)|^135 ≤ (38540117379041/50000000000000 : ℝ)^103
        have hw : |(8198638133/10000000000 : ℝ)|=(8198638133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49970511/250000000 : ℝ)|^135 ≤ (12121000021701/100000000000000 : ℝ)^103
        have hw : |(-49970511/250000000 : ℝ)|=(49970511/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1830207109/10000000000 : ℝ)|^135 ≤ (1349845649833/12500000000000 : ℝ)^103
        have hw : |(-1830207109/10000000000 : ℝ)|=(1830207109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s1_s1_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (438739961/2000000000 : ℝ)*x 0 + (-680726193/5000000000 : ℝ)*x 1 + (1670467011/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438739961/2000000000 : ℝ)^135 ≤ (2738573362869/20000000000000 : ℝ)^103 := by
    have hnat : (438739961 : ℕ)^135*20000000000000^103 ≤ 2738573362869^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438739961 2000000000 2738573362869 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680726193/5000000000 : ℝ)^135 ≤ (457967537359/6250000000000 : ℝ)^103 := by
    have hnat : (680726193 : ℕ)^135*6250000000000^103 ≤ 457967537359^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680726193 5000000000 457967537359 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1670467011/2000000000 : ℝ)^135 ≤ (39489826284317/50000000000000 : ℝ)^103 := by
    have hnat : (1670467011 : ℕ)^135*50000000000000^103 ≤ 39489826284317^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1670467011 2000000000 39489826284317 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(438739961/2000000000 : ℝ), (-680726193/5000000000 : ℝ), (1670467011/2000000000 : ℝ)] ![(2738573362869/20000000000000 : ℝ), (457967537359/6250000000000 : ℝ), (39489826284317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(438739961/2000000000 : ℝ)|^135 ≤ (2738573362869/20000000000000 : ℝ)^103
        have hw : |(438739961/2000000000 : ℝ)|=(438739961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-680726193/5000000000 : ℝ)|^135 ≤ (457967537359/6250000000000 : ℝ)^103
        have hw : |(-680726193/5000000000 : ℝ)|=(680726193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1670467011/2000000000 : ℝ)|^135 ≤ (39489826284317/50000000000000 : ℝ)^103
        have hw : |(1670467011/2000000000 : ℝ)|=(1670467011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s1_s1_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (23052513/10000000000 : ℝ)*x 0 + (-427089059/500000000 : ℝ)*x 1 + (2774505301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23052513/10000000000 : ℝ)^135 ≤ (4367959739/12500000000000 : ℝ)^103 := by
    have hnat : (23052513 : ℕ)^135*12500000000000^103 ≤ 4367959739^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23052513 10000000000 4367959739 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427089059/500000000 : ℝ)^135 ≤ (81335836601843/100000000000000 : ℝ)^103 := by
    have hnat : (427089059 : ℕ)^135*100000000000000^103 ≤ 81335836601843^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427089059 500000000 81335836601843 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2774505301/10000000000 : ℝ)^135 ≤ (291081557881/1562500000000 : ℝ)^103 := by
    have hnat : (2774505301 : ℕ)^135*1562500000000^103 ≤ 291081557881^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2774505301 10000000000 291081557881 1562500000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(23052513/10000000000 : ℝ), (-427089059/500000000 : ℝ), (2774505301/10000000000 : ℝ)] ![(4367959739/12500000000000 : ℝ), (81335836601843/100000000000000 : ℝ), (291081557881/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(23052513/10000000000 : ℝ)|^135 ≤ (4367959739/12500000000000 : ℝ)^103
        have hw : |(23052513/10000000000 : ℝ)|=(23052513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427089059/500000000 : ℝ)|^135 ≤ (81335836601843/100000000000000 : ℝ)^103
        have hw : |(-427089059/500000000 : ℝ)|=(427089059/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2774505301/10000000000 : ℝ)|^135 ≤ (291081557881/1562500000000 : ℝ)^103
        have hw : |(2774505301/10000000000 : ℝ)|=(2774505301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s1_s1_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (109706843/125000000 : ℝ)*x 0 + (1355638503/10000000000 : ℝ)*x 1 + (1515836973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109706843/125000000 : ℝ)^135 ≤ (84278255074339/100000000000000 : ℝ)^103 := by
    have hnat : (109706843 : ℕ)^135*100000000000000^103 ≤ 84278255074339^103*125000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109706843 125000000 84278255074339 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355638503/10000000000 : ℝ)^135 ≤ (7286495442877/100000000000000 : ℝ)^103 := by
    have hnat : (1355638503 : ℕ)^135*100000000000000^103 ≤ 7286495442877^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355638503 10000000000 7286495442877 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1515836973/10000000000 : ℝ)^135 ≤ (4217624736373/50000000000000 : ℝ)^103 := by
    have hnat : (1515836973 : ℕ)^135*50000000000000^103 ≤ 4217624736373^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1515836973 10000000000 4217624736373 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109706843/125000000 : ℝ), (1355638503/10000000000 : ℝ), (1515836973/10000000000 : ℝ)] ![(84278255074339/100000000000000 : ℝ), (7286495442877/100000000000000 : ℝ), (4217624736373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109706843/125000000 : ℝ)|^135 ≤ (84278255074339/100000000000000 : ℝ)^103
        have hw : |(109706843/125000000 : ℝ)|=(109706843/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355638503/10000000000 : ℝ)|^135 ≤ (7286495442877/100000000000000 : ℝ)^103
        have hw : |(1355638503/10000000000 : ℝ)|=(1355638503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1515836973/10000000000 : ℝ)|^135 ≤ (4217624736373/50000000000000 : ℝ)^103
        have hw : |(1515836973/10000000000 : ℝ)|=(1515836973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s1_s1_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1187292123/2500000000 : ℝ)*x 0 + (-869841617/2500000000 : ℝ)*x 1 + (-4707684333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1187292123/2500000000 : ℝ)^135 ≤ (37683328175387/100000000000000 : ℝ)^103 := by
    have hnat : (1187292123 : ℕ)^135*100000000000000^103 ≤ 37683328175387^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187292123 2500000000 37683328175387 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (869841617/2500000000 : ℝ)^135 ≤ (25064187208833/100000000000000 : ℝ)^103 := by
    have hnat : (869841617 : ℕ)^135*100000000000000^103 ≤ 25064187208833^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869841617 2500000000 25064187208833 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4707684333/10000000000 : ℝ)^135 ≤ (18626242297643/50000000000000 : ℝ)^103 := by
    have hnat : (4707684333 : ℕ)^135*50000000000000^103 ≤ 18626242297643^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4707684333 10000000000 18626242297643 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1187292123/2500000000 : ℝ), (-869841617/2500000000 : ℝ), (-4707684333/10000000000 : ℝ)] ![(37683328175387/100000000000000 : ℝ), (25064187208833/100000000000000 : ℝ), (18626242297643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1187292123/2500000000 : ℝ)|^135 ≤ (37683328175387/100000000000000 : ℝ)^103
        have hw : |(1187292123/2500000000 : ℝ)|=(1187292123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-869841617/2500000000 : ℝ)|^135 ≤ (25064187208833/100000000000000 : ℝ)^103
        have hw : |(-869841617/2500000000 : ℝ)|=(869841617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4707684333/10000000000 : ℝ)|^135 ≤ (18626242297643/50000000000000 : ℝ)^103
        have hw : |(-4707684333/10000000000 : ℝ)|=(4707684333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s1_s1_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (927297821/1250000000 : ℝ)*x 0 + (-944007329/10000000000 : ℝ)*x 1 + (1885591113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (927297821/1250000000 : ℝ)^135 ≤ (33805467900287/50000000000000 : ℝ)^103 := by
    have hnat : (927297821 : ℕ)^135*50000000000000^103 ≤ 33805467900287^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927297821 1250000000 33805467900287 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (944007329/10000000000 : ℝ)^135 ≤ (2267206694011/50000000000000 : ℝ)^103 := by
    have hnat : (944007329 : ℕ)^135*50000000000000^103 ≤ 2267206694011^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944007329 10000000000 2267206694011 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1885591113/5000000000 : ℝ)^135 ≤ (13927325395999/50000000000000 : ℝ)^103 := by
    have hnat : (1885591113 : ℕ)^135*50000000000000^103 ≤ 13927325395999^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885591113 5000000000 13927325395999 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(927297821/1250000000 : ℝ), (-944007329/10000000000 : ℝ), (1885591113/5000000000 : ℝ)] ![(33805467900287/50000000000000 : ℝ), (2267206694011/50000000000000 : ℝ), (13927325395999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(927297821/1250000000 : ℝ)|^135 ≤ (33805467900287/50000000000000 : ℝ)^103
        have hw : |(927297821/1250000000 : ℝ)|=(927297821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-944007329/10000000000 : ℝ)|^135 ≤ (2267206694011/50000000000000 : ℝ)^103
        have hw : |(-944007329/10000000000 : ℝ)|=(944007329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1885591113/5000000000 : ℝ)|^135 ≤ (13927325395999/50000000000000 : ℝ)^103
        have hw : |(1885591113/5000000000 : ℝ)|=(1885591113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306086_s1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((90383/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(90383/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-5951/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-5951/6250 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(94049/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(94049/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((76841/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76841/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-88247/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-88247/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43451/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43451/50000 : ℝ)*X 1 2) := by
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
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (90383/100000 : ℝ) ^ (67/16 : ℝ) ≤ (32740347143797601483/50000000000000000000 : ℝ) := by
    have hpowers : (90383/100000 : ℝ)^67 ≤ (32740347143797601483/50000000000000000000 : ℝ)^16 := by
      have hnat : (90383 : ℕ)^67*50000000000000000000^16 ≤ 32740347143797601483^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        90383 100000 32740347143797601483 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (90383/100000 : ℝ)) (X := (32740347143797601483/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (82740347143797601483/50000000000000000000 : ℝ) ≤ (5639078933836879/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (82740347143797601483/50000000000000000000 : ℝ)^16 ≤ (5639078933836879/5000000000000000 : ℝ)^67 := by
      have hnat : (82740347143797601483 : ℕ)^16*5000000000000000^67 ≤ 5639078933836879^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82740347143797601483 50000000000000000000 5639078933836879 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5639078933836879/5000000000000000 : ℝ)) (X := (82740347143797601483/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (57740347143797601483/25000000000000000000 : ℝ) ≤ (12212803648719277/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (57740347143797601483/25000000000000000000 : ℝ)^16 ≤ (12212803648719277/10000000000000000 : ℝ)^67 := by
      have hnat : (57740347143797601483 : ℕ)^16*10000000000000000^67 ≤ 12212803648719277^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57740347143797601483 25000000000000000000 12212803648719277 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12212803648719277/10000000000000000 : ℝ)) (X := (57740347143797601483/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(639078933836879/4519150000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(934645781045519/9038300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (90383/100000 : ℝ)) (alpha := (639078933836879/4519150000000000 : ℝ)) (beta := (934645781045519/9038300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (90383/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(639078933836879/4519150000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(934645781045519/9038300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (5951/6250 : ℝ) ^ (67/16 : ℝ) ≤ (8144189008266991177/10000000000000000000 : ℝ) := by
    have hpowers : (5951/6250 : ℝ)^67 ≤ (8144189008266991177/10000000000000000000 : ℝ)^16 := by
      have hnat : (5951 : ℕ)^67*10000000000000000000^16 ≤ 8144189008266991177^16*6250^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5951 6250 8144189008266991177 10000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5951/6250 : ℝ)) (X := (8144189008266991177/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (18144189008266991177/10000000000000000000 : ℝ) ≤ (1152890536617597/1000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (18144189008266991177/10000000000000000000 : ℝ)^16 ≤ (1152890536617597/1000000000000000 : ℝ)^67 := by
      have hnat : (18144189008266991177 : ℕ)^16*1000000000000000^67 ≤ 1152890536617597^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18144189008266991177 10000000000000000000 1152890536617597 1000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1152890536617597/1000000000000000 : ℝ)) (X := (18144189008266991177/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (13144189008266991177/5000000000000000000 : ℝ) ≤ (1259627400955431/1000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (13144189008266991177/5000000000000000000 : ℝ)^16 ≤ (1259627400955431/1000000000000000 : ℝ)^67 := by
      have hnat : (13144189008266991177 : ℕ)^16*1000000000000000^67 ≤ 1259627400955431^67*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13144189008266991177 5000000000000000000 1259627400955431 1000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1259627400955431/1000000000000000 : ℝ)) (X := (13144189008266991177/5000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(152890536617597/952160000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(53368432168917/476080000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (5951/6250 : ℝ)) (alpha := (152890536617597/952160000000000 : ℝ)) (beta := (53368432168917/476080000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (5951/6250 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(152890536617597/952160000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(53368432168917/476080000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (94049/100000 : ℝ) ^ (67/16 : ℝ) ≤ (77342933078330529811/100000000000000000000 : ℝ) := by
    have hpowers : (94049/100000 : ℝ)^67 ≤ (77342933078330529811/100000000000000000000 : ℝ)^16 := by
      have hnat : (94049 : ℕ)^67*100000000000000000000^16 ≤ 77342933078330529811^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        94049 100000 77342933078330529811 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (94049/100000 : ℝ)) (X := (77342933078330529811/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (177342933078330529811/100000000000000000000 : ℝ) ≤ (11466166441998797/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (177342933078330529811/100000000000000000000 : ℝ)^16 ≤ (11466166441998797/10000000000000000 : ℝ)^67 := by
      have hnat : (177342933078330529811 : ℕ)^16*10000000000000000^67 ≤ 11466166441998797^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        177342933078330529811 100000000000000000000 11466166441998797 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11466166441998797/10000000000000000 : ℝ)) (X := (177342933078330529811/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (127342933078330529811/50000000000000000000 : ℝ) ≤ (6250667321007701/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (127342933078330529811/50000000000000000000 : ℝ)^16 ≤ (6250667321007701/5000000000000000 : ℝ)^67 := by
      have hnat : (127342933078330529811 : ℕ)^16*5000000000000000^67 ≤ 6250667321007701^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127342933078330529811 50000000000000000000 6250667321007701 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6250667321007701/5000000000000000 : ℝ)) (X := (127342933078330529811/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1466166441998797/9404900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(207033640003321/1880980000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (94049/100000 : ℝ)) (alpha := (1466166441998797/9404900000000000 : ℝ)) (beta := (207033640003321/1880980000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (94049/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1466166441998797/9404900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(207033640003321/1880980000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((408649639/625000000 : ℝ)*X 1 0+(628161439/2000000000 : ℝ)*X 1 1+(3016218751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((6216459283/10000000000 : ℝ)*X 2 0+(-850293513/2500000000 : ℝ)*X 2 1+(-788623197/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1795395173/5000000000 : ℝ)*X 0 0+(-1267757447/5000000000 : ℝ)*X 0 1+(32703103/50000000 : ℝ)*X 0 2+(1795395173/5000000000 : ℝ)*X 1 0+(-1267757447/5000000000 : ℝ)*X 1 1+(32703103/50000000 : ℝ)*X 1 2+(1795395173/5000000000 : ℝ)*X 2 0+(-1267757447/5000000000 : ℝ)*X 2 1+(32703103/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((85614573/10000000000 : ℝ)*X 0 0+(-4176417409/5000000000 : ℝ)*X 0 1+(604005847/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((3792116349/10000000000 : ℝ)*X 1 0+(6518016367/10000000000 : ℝ)*X 1 1+(2337145129/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((8937597963/10000000000 : ℝ)*X 2 0+(-547229887/10000000000 : ℝ)*X 2 1+(-239548659/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((450778729/1250000000 : ℝ)*X 0 0+(-629504953/5000000000 : ℝ)*X 0 1+(368853451/500000000 : ℝ)*X 0 2+(450778729/1250000000 : ℝ)*X 1 0+(-629504953/5000000000 : ℝ)*X 1 1+(368853451/500000000 : ℝ)*X 1 2+(450778729/1250000000 : ℝ)*X 2 0+(-629504953/5000000000 : ℝ)*X 2 1+(368853451/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-96079/10000000000 : ℝ)*X 0 0+(-400181591/1000000000 : ℝ)*X 0 1+(237767399/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4358807543/5000000000 : ℝ)*X 1 0+(2087404081/10000000000 : ℝ)*X 1 1+(159422653/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((8198638133/10000000000 : ℝ)*X 2 0+(-49970511/250000000 : ℝ)*X 2 1+(-1830207109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((438739961/2000000000 : ℝ)*X 0 0+(-680726193/5000000000 : ℝ)*X 0 1+(1670467011/2000000000 : ℝ)*X 0 2+(438739961/2000000000 : ℝ)*X 1 0+(-680726193/5000000000 : ℝ)*X 1 1+(1670467011/2000000000 : ℝ)*X 1 2+(438739961/2000000000 : ℝ)*X 2 0+(-680726193/5000000000 : ℝ)*X 2 1+(1670467011/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((23052513/10000000000 : ℝ)*X 0 0+(-427089059/500000000 : ℝ)*X 0 1+(2774505301/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((109706843/125000000 : ℝ)*X 1 0+(1355638503/10000000000 : ℝ)*X 1 1+(1515836973/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1187292123/2500000000 : ℝ)*X 2 0+(-869841617/2500000000 : ℝ)*X 2 1+(-4707684333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((927297821/1250000000 : ℝ)*X 0 0+(-944007329/10000000000 : ℝ)*X 0 1+(1885591113/5000000000 : ℝ)*X 0 2+(927297821/1250000000 : ℝ)*X 1 0+(-944007329/10000000000 : ℝ)*X 1 1+(1885591113/5000000000 : ℝ)*X 1 2+(927297821/1250000000 : ℝ)*X 2 0+(-944007329/10000000000 : ℝ)*X 2 1+(1885591113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((76841/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76841/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1782586366285147556930778290523/632325793680212500000000000000000000 : ℝ) := by norm_num
    linear_combination (49161709119/100000000000 : ℝ)*(base7) + (6410414451/25000000000 : ℝ)*(base43) + (804019612529/1000000000000 : ℝ)*(base54) + (328253/1000000000000 : ℝ)*(base60) + (50783523997/31250000000 : ℝ)*(major_s1_0) + (171082023733/125000000000 : ℝ)*(major_s1_1) + (6568425243/8000000000 : ℝ)*(major_s1_2) + (7798369/500000000000 : ℝ)*(sp_s1_6) + (326988517313/200000000000 : ℝ)*(sp_s1_7) + (236422843809/125000000000 : ℝ)*(sp_s1_8) + (103861870241/125000000000 : ℝ)*(sp_s1_9) + (4634693521/6250000000 : ℝ)*(sp_s1_13) + (25798987/500000000000 : ℝ)*(sp_s1_16) + (23585867/1000000000000 : ℝ)*(sp_s1_21) + (1053969081437/1000000000000 : ℝ)*(f.failure) + (236422843809/125000000000 : ℝ)*(f.sum) + (5812282475060958229/11193711980000000000000000000000 : ℝ)*base62 + (312906000845501/1880980000000000000000000000 : ℝ)*base65 + (34907223837683/119020000000000000000000000 : ℝ)*base66 + (1761350768363633/1880980000000000000000000000 : ℝ)*base68 + (392916173663062851397/850043076700000000000000000000000 : ℝ)*base70 + (143875326448679/564893750000000000000000000 : ℝ)*base72 + (4708494175213/59510000000000000000000000 : ℝ)*base74 + (345165180846059/1129787500000000000000000000 : ℝ)*base77 + (15194961469700168649/53786923300000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (22641/50000000000000000 : ℝ)*base87 + (22641/50000000000000000 : ℝ)*base89 + (22641/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-88247/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-88247/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (100835235386129080296678249/13446730825000000000000000000000 : ℝ) := by norm_num
    linear_combination (927807758723/1000000000000 : ℝ)*(base7) + (123245329431/500000000000 : ℝ)*(base33) + (1019303/500000000000 : ℝ)*(base40) + (686187687623/500000000000 : ℝ)*(major_s1_0) + (404716508527/250000000000 : ℝ)*(major_s1_1) + (404716508527/250000000000 : ℝ)*(major_s1_2) + (21017277/1000000000000 : ℝ)*(sp_s1_1) + (1071147/40000000000 : ℝ)*(sp_s1_2) + (13878309/1000000000000 : ℝ)*(sp_s1_13) + (403140929393/250000000000 : ℝ)*(sp_s1_14) + (1366029818953/1000000000000 : ℝ)*(sp_s1_15) + (273209256007/200000000000 : ℝ)*(sp_s1_16) + (1977737477179/1000000000000 : ℝ)*(sp_s1_20) + (22222481/1000000000000 : ℝ)*(sp_s1_22) + (209988719353/200000000000 : ℝ)*(f.failure) + (403140929393/250000000000 : ℝ)*(f.sum) + (4380519764240208681/55968559900000000000000000000000 : ℝ)*base63 + (141044805057251/470245000000000000000000000 : ℝ)*base64 + (19774106602507/47608000000000000000000000 : ℝ)*base67 + (2386915458624067/4702450000000000000000000000 : ℝ)*base68 + (135798201813426780851/425021538350000000000000000000000 : ℝ)*base71 + (1073716203241813/4519150000000000000000000000 : ℝ)*base72 + (40572870327833/119020000000000000000000000 : ℝ)*base75 + (92456361503327/2259575000000000000000000000 : ℝ)*base77 + (56186331057916828267/107573846600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (829/10000000000000000 : ℝ)*base87 + (829/10000000000000000 : ℝ)*base89 + (829/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43451/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43451/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (902898065460267177366758499/85004307670000000000000000000000 : ℝ) := by norm_num
    linear_combination (721508148053/1000000000000 : ℝ)*(base7) + (975953/500000000000 : ℝ)*(base15) + (2321076341/100000000000 : ℝ)*(base40) + (46993100891/50000000000 : ℝ)*(base43) + (305321/250000000000 : ℝ)*(base50) + (67068584761/40000000000 : ℝ)*(major_s1_0) + (147370520241/200000000000 : ℝ)*(major_s1_1) + (67068584761/40000000000 : ℝ)*(major_s1_2) + (10536719/500000000000 : ℝ)*(sp_s1_2) + (2530593/1000000000000 : ℝ)*(sp_s1_7) + (439389114627/500000000000 : ℝ)*(sp_s1_21) + (1818640825761/1000000000000 : ℝ)*(sp_s1_22) + (878759686409/1000000000000 : ℝ)*(sp_s1_23) + (904485223101/500000000000 : ℝ)*(sp_s1_27) + (1087462298149/1000000000000 : ℝ)*(f.failure) + (1818642777667/1000000000000 : ℝ)*(f.sum) + (5697381278735631379/44774847920000000000000000000000 : ℝ)*base62 + (50955946836671/1880980000000000000000000000 : ℝ)*base65 + (523662287837809/952160000000000000000000000 : ℝ)*base67 + (61842717934137/1880980000000000000000000000 : ℝ)*base69 + (12009078736502314437/34001723068000000000000000000000 : ℝ)*base71 + (19644853164527/361532000000000000000000000 : ℝ)*base72 + (49524593592841/476080000000000000000000000 : ℝ)*base75 + (426633352566013/903830000000000000000000000 : ℝ)*base77 + (14694792057966573593/86059077280000000000000000000000 : ℝ)*base78 + (49143/50000000000000000 : ℝ)*base86 + (49143/50000000000000000 : ℝ)*base88 + (49143/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((90383/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(90383/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-5951/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-5951/6250 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(94049/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(94049/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((76841/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76841/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-88247/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-88247/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43451/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43451/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306086_s1 p hpa hpb X hX hprev0

#print axioms solution

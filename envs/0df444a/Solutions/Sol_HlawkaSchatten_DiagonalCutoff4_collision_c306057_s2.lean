-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306057_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:56:22.141269+00:00
-- url     : https://prove2.me/submissions/27ba1f5a-6486-4e6c-9ae0-ce793a61a228

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
theorem collision_support_c306057_s2_s2_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-396495631/1250000000 : ℝ)*x 0 + (1584599911/5000000000 : ℝ)*x 1 + (1278360099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396495631/1250000000 : ℝ)^135 ≤ (4440494001/20000000000 : ℝ)^103 := by
    have hnat : (396495631 : ℕ)^135*20000000000^103 ≤ 4440494001^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396495631 1250000000 4440494001 20000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1584599911/5000000000 : ℝ)^135 ≤ (11088552316203/50000000000000 : ℝ)^103 := by
    have hnat : (1584599911 : ℕ)^135*50000000000000^103 ≤ 11088552316203^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584599911 5000000000 11088552316203 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1278360099/2000000000 : ℝ)^135 ≤ (55620425347149/100000000000000 : ℝ)^103 := by
    have hnat : (1278360099 : ℕ)^135*100000000000000^103 ≤ 55620425347149^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278360099 2000000000 55620425347149 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-396495631/1250000000 : ℝ), (1584599911/5000000000 : ℝ), (1278360099/2000000000 : ℝ)] ![(4440494001/20000000000 : ℝ), (11088552316203/50000000000000 : ℝ), (55620425347149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-396495631/1250000000 : ℝ)|^135 ≤ (4440494001/20000000000 : ℝ)^103
        have hw : |(-396495631/1250000000 : ℝ)|=(396495631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1584599911/5000000000 : ℝ)|^135 ≤ (11088552316203/50000000000000 : ℝ)^103
        have hw : |(1584599911/5000000000 : ℝ)|=(1584599911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1278360099/2000000000 : ℝ)|^135 ≤ (55620425347149/100000000000000 : ℝ)^103
        have hw : |(1278360099/2000000000 : ℝ)|=(1278360099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s2_s2_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (24766727/78125000 : ℝ)*x 0 + (-158368871/500000000 : ℝ)*x 1 + (6394732717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24766727/78125000 : ℝ)^135 ≤ (11092868892403/50000000000000 : ℝ)^103 := by
    have hnat : (24766727 : ℕ)^135*50000000000000^103 ≤ 11092868892403^103*78125000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24766727 78125000 11092868892403 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (158368871/500000000 : ℝ)^135 ≤ (5540097881779/25000000000000 : ℝ)^103 := by
    have hnat : (158368871 : ℕ)^135*25000000000000^103 ≤ 5540097881779^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158368871 500000000 5540097881779 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6394732717/10000000000 : ℝ)^135 ≤ (13913467668231/25000000000000 : ℝ)^103 := by
    have hnat : (6394732717 : ℕ)^135*25000000000000^103 ≤ 13913467668231^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6394732717 10000000000 13913467668231 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(24766727/78125000 : ℝ), (-158368871/500000000 : ℝ), (6394732717/10000000000 : ℝ)] ![(11092868892403/50000000000000 : ℝ), (5540097881779/25000000000000 : ℝ), (13913467668231/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(24766727/78125000 : ℝ)|^135 ≤ (11092868892403/50000000000000 : ℝ)^103
        have hw : |(24766727/78125000 : ℝ)|=(24766727/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-158368871/500000000 : ℝ)|^135 ≤ (5540097881779/25000000000000 : ℝ)^103
        have hw : |(-158368871/500000000 : ℝ)|=(158368871/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6394732717/10000000000 : ℝ)|^135 ≤ (13913467668231/25000000000000 : ℝ)^103
        have hw : |(6394732717/10000000000 : ℝ)|=(6394732717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s2_s2_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2412061523/5000000000 : ℝ)*x 0 + (4827400973/10000000000 : ℝ)*x 1 + (3262448353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2412061523/5000000000 : ℝ)^135 ≤ (7692950117457/20000000000000 : ℝ)^103 := by
    have hnat : (2412061523 : ℕ)^135*20000000000000^103 ≤ 7692950117457^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2412061523 5000000000 7692950117457 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4827400973/10000000000 : ℝ)^135 ≤ (38499010495591/100000000000000 : ℝ)^103 := by
    have hnat : (4827400973 : ℕ)^135*100000000000000^103 ≤ 38499010495591^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4827400973 10000000000 38499010495591 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3262448353/10000000000 : ℝ)^135 ≤ (5759059725201/25000000000000 : ℝ)^103 := by
    have hnat : (3262448353 : ℕ)^135*25000000000000^103 ≤ 5759059725201^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3262448353 10000000000 5759059725201 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2412061523/5000000000 : ℝ), (4827400973/10000000000 : ℝ), (3262448353/10000000000 : ℝ)] ![(7692950117457/20000000000000 : ℝ), (38499010495591/100000000000000 : ℝ), (5759059725201/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2412061523/5000000000 : ℝ)|^135 ≤ (7692950117457/20000000000000 : ℝ)^103
        have hw : |(2412061523/5000000000 : ℝ)|=(2412061523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4827400973/10000000000 : ℝ)|^135 ≤ (38499010495591/100000000000000 : ℝ)^103
        have hw : |(4827400973/10000000000 : ℝ)|=(4827400973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3262448353/10000000000 : ℝ)|^135 ≤ (5759059725201/25000000000000 : ℝ)^103
        have hw : |(3262448353/10000000000 : ℝ)|=(3262448353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s2_s2_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2446857217/10000000000 : ℝ)*x 0 + (1981055049/10000000000 : ℝ)*x 1 + (390058851/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2446857217/10000000000 : ℝ)^135 ≤ (15800171219421/100000000000000 : ℝ)^103 := by
    have hnat : (2446857217 : ℕ)^135*100000000000000^103 ≤ 15800171219421^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2446857217 10000000000 15800171219421 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1981055049/10000000000 : ℝ)^135 ≤ (11979994951143/100000000000000 : ℝ)^103 := by
    have hnat : (1981055049 : ℕ)^135*100000000000000^103 ≤ 11979994951143^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981055049 10000000000 11979994951143 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (390058851/500000000 : ℝ)^135 ≤ (3610991690577/5000000000000 : ℝ)^103 := by
    have hnat : (390058851 : ℕ)^135*5000000000000^103 ≤ 3610991690577^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390058851 500000000 3610991690577 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2446857217/10000000000 : ℝ), (1981055049/10000000000 : ℝ), (390058851/500000000 : ℝ)] ![(15800171219421/100000000000000 : ℝ), (11979994951143/100000000000000 : ℝ), (3610991690577/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2446857217/10000000000 : ℝ)|^135 ≤ (15800171219421/100000000000000 : ℝ)^103
        have hw : |(-2446857217/10000000000 : ℝ)|=(2446857217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1981055049/10000000000 : ℝ)|^135 ≤ (11979994951143/100000000000000 : ℝ)^103
        have hw : |(1981055049/10000000000 : ℝ)|=(1981055049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(390058851/500000000 : ℝ)|^135 ≤ (3610991690577/5000000000000 : ℝ)^103
        have hw : |(390058851/500000000 : ℝ)|=(390058851/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s2_s2_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2444008979/10000000000 : ℝ)*x 0 + (-1978749023/10000000000 : ℝ)*x 1 + (3902334603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2444008979/10000000000 : ℝ)^135 ≤ (15776069533207/100000000000000 : ℝ)^103 := by
    have hnat : (2444008979 : ℕ)^135*100000000000000^103 ≤ 15776069533207^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2444008979 10000000000 15776069533207 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1978749023/10000000000 : ℝ)^135 ≤ (11961720586913/100000000000000 : ℝ)^103 := by
    have hnat : (1978749023 : ℕ)^135*100000000000000^103 ≤ 11961720586913^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978749023 10000000000 11961720586913 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3902334603/5000000000 : ℝ)^135 ≤ (7226220986017/10000000000000 : ℝ)^103 := by
    have hnat : (3902334603 : ℕ)^135*10000000000000^103 ≤ 7226220986017^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3902334603 5000000000 7226220986017 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2444008979/10000000000 : ℝ), (-1978749023/10000000000 : ℝ), (3902334603/5000000000 : ℝ)] ![(15776069533207/100000000000000 : ℝ), (11961720586913/100000000000000 : ℝ), (7226220986017/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2444008979/10000000000 : ℝ)|^135 ≤ (15776069533207/100000000000000 : ℝ)^103
        have hw : |(2444008979/10000000000 : ℝ)|=(2444008979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1978749023/10000000000 : ℝ)|^135 ≤ (11961720586913/100000000000000 : ℝ)^103
        have hw : |(-1978749023/10000000000 : ℝ)|=(1978749023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3902334603/5000000000 : ℝ)|^135 ≤ (7226220986017/10000000000000 : ℝ)^103
        have hw : |(3902334603/5000000000 : ℝ)|=(3902334603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s2_s2_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4018671079/10000000000 : ℝ)*x 0 + (1898685231/2500000000 : ℝ)*x 1 + (439/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4018671079/10000000000 : ℝ)^135 ≤ (30274637679013/100000000000000 : ℝ)^103 := by
    have hnat : (4018671079 : ℕ)^135*100000000000000^103 ≤ 30274637679013^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018671079 10000000000 30274637679013 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1898685231/2500000000 : ℝ)^135 ≤ (8715670245301/12500000000000 : ℝ)^103 := by
    have hnat : (1898685231 : ℕ)^135*12500000000000^103 ≤ 8715670245301^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898685231 2500000000 8715670245301 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439/1250000000 : ℝ)^135 ≤ (346969/100000000000000 : ℝ)^103 := by
    have hnat : (439 : ℕ)^135*100000000000000^103 ≤ 346969^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439 1250000000 346969 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4018671079/10000000000 : ℝ), (1898685231/2500000000 : ℝ), (439/1250000000 : ℝ)] ![(30274637679013/100000000000000 : ℝ), (8715670245301/12500000000000 : ℝ), (346969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4018671079/10000000000 : ℝ)|^135 ≤ (30274637679013/100000000000000 : ℝ)^103
        have hw : |(4018671079/10000000000 : ℝ)|=(4018671079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1898685231/2500000000 : ℝ)|^135 ≤ (8715670245301/12500000000000 : ℝ)^103
        have hw : |(1898685231/2500000000 : ℝ)|=(1898685231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(439/1250000000 : ℝ)|^135 ≤ (346969/100000000000000 : ℝ)^103
        have hw : |(439/1250000000 : ℝ)|=(439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s2_s2_12 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1823048973/5000000000 : ℝ)*x 0 + (1722657113/2500000000 : ℝ)*x 1 + (990054643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1823048973/5000000000 : ℝ)^135 ≤ (26650006978197/100000000000000 : ℝ)^103 := by
    have hnat : (1823048973 : ℕ)^135*100000000000000^103 ≤ 26650006978197^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823048973 5000000000 26650006978197 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1722657113/2500000000 : ℝ)^135 ≤ (3068874683031/5000000000000 : ℝ)^103 := by
    have hnat : (1722657113 : ℕ)^135*5000000000000^103 ≤ 3068874683031^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722657113 2500000000 3068874683031 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (990054643/5000000000 : ℝ)^135 ≤ (11972499345271/100000000000000 : ℝ)^103 := by
    have hnat : (990054643 : ℕ)^135*100000000000000^103 ≤ 11972499345271^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990054643 5000000000 11972499345271 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1823048973/5000000000 : ℝ), (1722657113/2500000000 : ℝ), (990054643/5000000000 : ℝ)] ![(26650006978197/100000000000000 : ℝ), (3068874683031/5000000000000 : ℝ), (11972499345271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1823048973/5000000000 : ℝ)|^135 ≤ (26650006978197/100000000000000 : ℝ)^103
        have hw : |(1823048973/5000000000 : ℝ)|=(1823048973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1722657113/2500000000 : ℝ)|^135 ≤ (3068874683031/5000000000000 : ℝ)^103
        have hw : |(1722657113/2500000000 : ℝ)|=(1722657113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(990054643/5000000000 : ℝ)|^135 ≤ (11972499345271/100000000000000 : ℝ)^103
        have hw : |(990054643/5000000000 : ℝ)|=(990054643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s2_s2_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-991967091/5000000000 : ℝ)*x 0 + (2443885581/10000000000 : ℝ)*x 1 + (1560273651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (991967091/5000000000 : ℝ)^135 ≤ (2400564048871/20000000000000 : ℝ)^103 := by
    have hnat : (991967091 : ℕ)^135*20000000000000^103 ≤ 2400564048871^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991967091 5000000000 2400564048871 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2443885581/10000000000 : ℝ)^135 ≤ (7887512770481/50000000000000 : ℝ)^103 := by
    have hnat : (2443885581 : ℕ)^135*50000000000000^103 ≤ 7887512770481^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2443885581 10000000000 7887512770481 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1560273651/2000000000 : ℝ)^135 ≤ (36111077103293/50000000000000 : ℝ)^103 := by
    have hnat : (1560273651 : ℕ)^135*50000000000000^103 ≤ 36111077103293^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560273651 2000000000 36111077103293 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-991967091/5000000000 : ℝ), (2443885581/10000000000 : ℝ), (1560273651/2000000000 : ℝ)] ![(2400564048871/20000000000000 : ℝ), (7887512770481/50000000000000 : ℝ), (36111077103293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-991967091/5000000000 : ℝ)|^135 ≤ (2400564048871/20000000000000 : ℝ)^103
        have hw : |(-991967091/5000000000 : ℝ)|=(991967091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2443885581/10000000000 : ℝ)|^135 ≤ (7887512770481/50000000000000 : ℝ)^103
        have hw : |(2443885581/10000000000 : ℝ)|=(2443885581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1560273651/2000000000 : ℝ)|^135 ≤ (36111077103293/50000000000000 : ℝ)^103
        have hw : |(1560273651/2000000000 : ℝ)|=(1560273651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s2_s2_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1981624473/10000000000 : ℝ)*x 0 + (-1220520197/5000000000 : ℝ)*x 1 + (7804860623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1981624473/10000000000 : ℝ)^135 ≤ (11984508433949/100000000000000 : ℝ)^103 := by
    have hnat : (1981624473 : ℕ)^135*100000000000000^103 ≤ 11984508433949^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981624473 10000000000 11984508433949 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1220520197/5000000000 : ℝ)^135 ≤ (630038350429/4000000000000 : ℝ)^103 := by
    have hnat : (1220520197 : ℕ)^135*4000000000000^103 ≤ 630038350429^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220520197 5000000000 630038350429 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7804860623/10000000000 : ℝ)^135 ≤ (2258266649579/3125000000000 : ℝ)^103 := by
    have hnat : (7804860623 : ℕ)^135*3125000000000^103 ≤ 2258266649579^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7804860623 10000000000 2258266649579 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1981624473/10000000000 : ℝ), (-1220520197/5000000000 : ℝ), (7804860623/10000000000 : ℝ)] ![(11984508433949/100000000000000 : ℝ), (630038350429/4000000000000 : ℝ), (2258266649579/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1981624473/10000000000 : ℝ)|^135 ≤ (11984508433949/100000000000000 : ℝ)^103
        have hw : |(1981624473/10000000000 : ℝ)|=(1981624473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1220520197/5000000000 : ℝ)|^135 ≤ (630038350429/4000000000000 : ℝ)^103
        have hw : |(-1220520197/5000000000 : ℝ)|=(1220520197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7804860623/10000000000 : ℝ)|^135 ≤ (2258266649579/3125000000000 : ℝ)^103
        have hw : |(7804860623/10000000000 : ℝ)|=(7804860623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s2_s2_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7591434891/10000000000 : ℝ)*x 0 + (2011349549/5000000000 : ℝ)*x 1 + (1749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7591434891/10000000000 : ℝ)^135 ≤ (6968558311723/10000000000000 : ℝ)^103 := by
    have hnat : (7591434891 : ℕ)^135*10000000000000^103 ≤ 6968558311723^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7591434891 10000000000 6968558311723 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2011349549/5000000000 : ℝ)^135 ≤ (6062883304389/20000000000000 : ℝ)^103 := by
    have hnat : (2011349549 : ℕ)^135*20000000000000^103 ≤ 6062883304389^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011349549 5000000000 6062883304389 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1749/5000000000 : ℝ)^135 ≤ (345157/100000000000000 : ℝ)^103 := by
    have hnat : (1749 : ℕ)^135*100000000000000^103 ≤ 345157^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1749 5000000000 345157 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7591434891/10000000000 : ℝ), (2011349549/5000000000 : ℝ), (1749/5000000000 : ℝ)] ![(6968558311723/10000000000000 : ℝ), (6062883304389/20000000000000 : ℝ), (345157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7591434891/10000000000 : ℝ)|^135 ≤ (6968558311723/10000000000000 : ℝ)^103
        have hw : |(7591434891/10000000000 : ℝ)|=(7591434891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2011349549/5000000000 : ℝ)|^135 ≤ (6062883304389/20000000000000 : ℝ)^103
        have hw : |(2011349549/5000000000 : ℝ)|=(2011349549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1749/5000000000 : ℝ)|^135 ≤ (345157/100000000000000 : ℝ)^103
        have hw : |(1749/5000000000 : ℝ)|=(1749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s2_s2_18 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6887673283/10000000000 : ℝ)*x 0 + (364977603/1000000000 : ℝ)*x 1 + (1980015521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6887673283/10000000000 : ℝ)^135 ≤ (61342995157897/100000000000000 : ℝ)^103 := by
    have hnat : (6887673283 : ℕ)^135*100000000000000^103 ≤ 61342995157897^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6887673283 10000000000 61342995157897 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364977603/1000000000 : ℝ)^135 ≤ (1667828034107/6250000000000 : ℝ)^103 := by
    have hnat : (364977603 : ℕ)^135*6250000000000^103 ≤ 1667828034107^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364977603 1000000000 1667828034107 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1980015521/10000000000 : ℝ)^135 ≤ (5985878137601/50000000000000 : ℝ)^103 := by
    have hnat : (1980015521 : ℕ)^135*50000000000000^103 ≤ 5985878137601^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980015521 10000000000 5985878137601 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6887673283/10000000000 : ℝ), (364977603/1000000000 : ℝ), (1980015521/10000000000 : ℝ)] ![(61342995157897/100000000000000 : ℝ), (1667828034107/6250000000000 : ℝ), (5985878137601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6887673283/10000000000 : ℝ)|^135 ≤ (61342995157897/100000000000000 : ℝ)^103
        have hw : |(6887673283/10000000000 : ℝ)|=(6887673283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(364977603/1000000000 : ℝ)|^135 ≤ (1667828034107/6250000000000 : ℝ)^103
        have hw : |(364977603/1000000000 : ℝ)|=(364977603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1980015521/10000000000 : ℝ)|^135 ≤ (5985878137601/50000000000000 : ℝ)^103
        have hw : |(1980015521/10000000000 : ℝ)|=(1980015521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s2_s2_19 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-921230579/2000000000 : ℝ)*x 0 + (396710071/2000000000 : ℝ)*x 1 + (3026888989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (921230579/2000000000 : ℝ)^135 ≤ (4525373735097/12500000000000 : ℝ)^103 := by
    have hnat : (921230579 : ℕ)^135*12500000000000^103 ≤ 4525373735097^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921230579 2000000000 4525373735097 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (396710071/2000000000 : ℝ)^135 ≤ (11999776732101/100000000000000 : ℝ)^103 := by
    have hnat : (396710071 : ℕ)^135*100000000000000^103 ≤ 11999776732101^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396710071 2000000000 11999776732101 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3026888989/5000000000 : ℝ)^135 ≤ (51797233366391/100000000000000 : ℝ)^103 := by
    have hnat : (3026888989 : ℕ)^135*100000000000000^103 ≤ 51797233366391^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3026888989 5000000000 51797233366391 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-921230579/2000000000 : ℝ), (396710071/2000000000 : ℝ), (3026888989/5000000000 : ℝ)] ![(4525373735097/12500000000000 : ℝ), (11999776732101/100000000000000 : ℝ), (51797233366391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-921230579/2000000000 : ℝ)|^135 ≤ (4525373735097/12500000000000 : ℝ)^103
        have hw : |(-921230579/2000000000 : ℝ)|=(921230579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(396710071/2000000000 : ℝ)|^135 ≤ (11999776732101/100000000000000 : ℝ)^103
        have hw : |(396710071/2000000000 : ℝ)|=(396710071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3026888989/5000000000 : ℝ)|^135 ≤ (51797233366391/100000000000000 : ℝ)^103
        have hw : |(3026888989/5000000000 : ℝ)|=(3026888989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s2_s2_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (992460929/5000000000 : ℝ)*x 0 + (-2300889343/5000000000 : ℝ)*x 1 + (6056825467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (992460929/5000000000 : ℝ)^135 ≤ (3002663187277/25000000000000 : ℝ)^103 := by
    have hnat : (992460929 : ℕ)^135*25000000000000^103 ≤ 3002663187277^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992460929 5000000000 3002663187277 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2300889343/5000000000 : ℝ)^135 ≤ (18078967695387/50000000000000 : ℝ)^103 := by
    have hnat : (2300889343 : ℕ)^135*50000000000000^103 ≤ 18078967695387^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2300889343 5000000000 18078967695387 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6056825467/10000000000 : ℝ)^135 ≤ (10366282368901/20000000000000 : ℝ)^103 := by
    have hnat : (6056825467 : ℕ)^135*20000000000000^103 ≤ 10366282368901^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6056825467 10000000000 10366282368901 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(992460929/5000000000 : ℝ), (-2300889343/5000000000 : ℝ), (6056825467/10000000000 : ℝ)] ![(3002663187277/25000000000000 : ℝ), (18078967695387/50000000000000 : ℝ), (10366282368901/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(992460929/5000000000 : ℝ)|^135 ≤ (3002663187277/25000000000000 : ℝ)^103
        have hw : |(992460929/5000000000 : ℝ)|=(992460929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2300889343/5000000000 : ℝ)|^135 ≤ (18078967695387/50000000000000 : ℝ)^103
        have hw : |(-2300889343/5000000000 : ℝ)|=(2300889343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6056825467/10000000000 : ℝ)|^135 ≤ (10366282368901/20000000000000 : ℝ)^103
        have hw : |(6056825467/10000000000 : ℝ)|=(6056825467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s2_s2_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6188240281/10000000000 : ℝ)*x 0 + (1117058477/2000000000 : ℝ)*x 1 + (44157561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6188240281/10000000000 : ℝ)^135 ≤ (13327581467729/25000000000000 : ℝ)^103 := by
    have hnat : (6188240281 : ℕ)^135*25000000000000^103 ≤ 13327581467729^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6188240281 10000000000 13327581467729 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1117058477/2000000000 : ℝ)^135 ≤ (2330388024113/5000000000000 : ℝ)^103 := by
    have hnat : (1117058477 : ℕ)^135*5000000000000^103 ≤ 2330388024113^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117058477 2000000000 2330388024113 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44157561/10000000000 : ℝ)^135 ≤ (81913629529/100000000000000 : ℝ)^103 := by
    have hnat : (44157561 : ℕ)^135*100000000000000^103 ≤ 81913629529^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44157561 10000000000 81913629529 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6188240281/10000000000 : ℝ), (1117058477/2000000000 : ℝ), (44157561/10000000000 : ℝ)] ![(13327581467729/25000000000000 : ℝ), (2330388024113/5000000000000 : ℝ), (81913629529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6188240281/10000000000 : ℝ)|^135 ≤ (13327581467729/25000000000000 : ℝ)^103
        have hw : |(6188240281/10000000000 : ℝ)|=(6188240281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1117058477/2000000000 : ℝ)|^135 ≤ (2330388024113/5000000000000 : ℝ)^103
        have hw : |(1117058477/2000000000 : ℝ)|=(1117058477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(44157561/10000000000 : ℝ)|^135 ≤ (81913629529/100000000000000 : ℝ)^103
        have hw : |(44157561/10000000000 : ℝ)|=(44157561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s2_s2_25 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1986048647/5000000000 : ℝ)*x 0 + (1117058477/2000000000 : ℝ)*x 1 + (830169867/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1986048647/5000000000 : ℝ)^135 ≤ (29815598329887/100000000000000 : ℝ)^103 := by
    have hnat : (1986048647 : ℕ)^135*100000000000000^103 ≤ 29815598329887^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986048647 5000000000 29815598329887 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1117058477/2000000000 : ℝ)^135 ≤ (2330388024113/5000000000000 : ℝ)^103 := by
    have hnat : (1117058477 : ℕ)^135*5000000000000^103 ≤ 2330388024113^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117058477 2000000000 2330388024113 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830169867/2500000000 : ℝ)^135 ≤ (23576641175451/100000000000000 : ℝ)^103 := by
    have hnat : (830169867 : ℕ)^135*100000000000000^103 ≤ 23576641175451^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830169867 2500000000 23576641175451 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1986048647/5000000000 : ℝ), (1117058477/2000000000 : ℝ), (830169867/2500000000 : ℝ)] ![(29815598329887/100000000000000 : ℝ), (2330388024113/5000000000000 : ℝ), (23576641175451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1986048647/5000000000 : ℝ)|^135 ≤ (29815598329887/100000000000000 : ℝ)^103
        have hw : |(1986048647/5000000000 : ℝ)|=(1986048647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1117058477/2000000000 : ℝ)|^135 ≤ (2330388024113/5000000000000 : ℝ)^103
        have hw : |(1117058477/2000000000 : ℝ)|=(1117058477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(830169867/2500000000 : ℝ)|^135 ≤ (23576641175451/100000000000000 : ℝ)^103
        have hw : |(830169867/2500000000 : ℝ)|=(830169867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306057_s2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((21501/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21501/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(429/500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(429/500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4879/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4879/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9277/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9277/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37091/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37091/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1321/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1321/6250 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (21501/25000 : ℝ) ^ (67/16 : ℝ) ≤ (53185941193139284133/100000000000000000000 : ℝ) := by
    have hpowers : (21501/25000 : ℝ)^67 ≤ (53185941193139284133/100000000000000000000 : ℝ)^16 := by
      have hnat : (21501 : ℕ)^67*100000000000000000000^16 ≤ 53185941193139284133^16*25000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21501 25000 53185941193139284133 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21501/25000 : ℝ)) (X := (53185941193139284133/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (153185941193139284133/100000000000000000000 : ℝ) ≤ (5536067613727047/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (153185941193139284133/100000000000000000000 : ℝ)^16 ≤ (5536067613727047/5000000000000000 : ℝ)^67 := by
      have hnat : (153185941193139284133 : ℕ)^16*5000000000000000^67 ≤ 5536067613727047^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        153185941193139284133 100000000000000000000 5536067613727047 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5536067613727047/5000000000000000 : ℝ)) (X := (153185941193139284133/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (103185941193139284133/50000000000000000000 : ℝ) ≤ (11888865777733113/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (103185941193139284133/50000000000000000000 : ℝ)^16 ≤ (11888865777733113/10000000000000000 : ℝ)^67 := by
      have hnat : (103185941193139284133 : ℕ)^16*10000000000000000^67 ≤ 11888865777733113^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103185941193139284133 50000000000000000000 11888865777733113 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11888865777733113/10000000000000000 : ℝ)) (X := (103185941193139284133/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(536067613727047/4300200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(90747838919891/955600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (21501/25000 : ℝ)) (alpha := (536067613727047/4300200000000000 : ℝ)) (beta := (90747838919891/955600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (21501/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(536067613727047/4300200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(90747838919891/955600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (429/500 : ℝ) ^ (67/16 : ℝ) ≤ (52659656014843321027/100000000000000000000 : ℝ) := by
    have hpowers : (429/500 : ℝ)^67 ≤ (52659656014843321027/100000000000000000000 : ℝ)^16 := by
      have hnat : (429 : ℕ)^67*100000000000000000000^16 ≤ 52659656014843321027^16*500^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        429 500 52659656014843321027 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (429/500 : ℝ)) (X := (52659656014843321027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (152659656014843321027/100000000000000000000 : ℝ) ≤ (2212607858103139/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (152659656014843321027/100000000000000000000 : ℝ)^16 ≤ (2212607858103139/2000000000000000 : ℝ)^67 := by
      have hnat : (152659656014843321027 : ℕ)^16*2000000000000000^67 ≤ 2212607858103139^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        152659656014843321027 100000000000000000000 2212607858103139 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2212607858103139/2000000000000000 : ℝ)) (X := (152659656014843321027/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (102659656014843321027/50000000000000000000 : ℝ) ≤ (11874356995292477/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (102659656014843321027/50000000000000000000 : ℝ)^16 ≤ (11874356995292477/10000000000000000 : ℝ)^67 := by
      have hnat : (102659656014843321027 : ℕ)^16*10000000000000000^67 ≤ 11874356995292477^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102659656014843321027 50000000000000000000 11874356995292477 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11874356995292477/10000000000000000 : ℝ)) (X := (102659656014843321027/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(212607858103139/1716000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(135219617462797/1430000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (429/500 : ℝ)) (alpha := (212607858103139/1716000000000000 : ℝ)) (beta := (135219617462797/1430000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (429/500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(212607858103139/1716000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(135219617462797/1430000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (4879/12500 : ℝ) ^ (67/16 : ℝ) ≤ (972847183061643213/50000000000000000000 : ℝ) := by
    have hpowers : (4879/12500 : ℝ)^67 ≤ (972847183061643213/50000000000000000000 : ℝ)^16 := by
      have hnat : (4879 : ℕ)^67*50000000000000000000^16 ≤ 972847183061643213^16*12500^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4879 12500 972847183061643213 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4879/12500 : ℝ)) (X := (972847183061643213/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (50972847183061643213/50000000000000000000 : ℝ) ≤ (5023062070501397/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (50972847183061643213/50000000000000000000 : ℝ)^16 ≤ (5023062070501397/5000000000000000 : ℝ)^67 := by
      have hnat : (50972847183061643213 : ℕ)^16*5000000000000000^67 ≤ 5023062070501397^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50972847183061643213 50000000000000000000 5023062070501397 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5023062070501397/5000000000000000 : ℝ)) (X := (50972847183061643213/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (25972847183061643213/25000000000000000000 : ℝ) ≤ (10091582986364191/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (25972847183061643213/25000000000000000000 : ℝ)^16 ≤ (10091582986364191/10000000000000000 : ℝ)^67 := by
      have hnat : (25972847183061643213 : ℕ)^16*10000000000000000^67 ≤ 10091582986364191^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25972847183061643213 25000000000000000000 10091582986364191 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10091582986364191/10000000000000000 : ℝ)) (X := (25972847183061643213/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(23062070501397/1951600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(2674049727141/229600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (4879/12500 : ℝ)) (alpha := (23062070501397/1951600000000000 : ℝ)) (beta := (2674049727141/229600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (4879/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(23062070501397/1951600000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(2674049727141/229600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-396495631/1250000000 : ℝ)*X 0 0+(1584599911/5000000000 : ℝ)*X 0 1+(1278360099/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((24766727/78125000 : ℝ)*X 1 0+(-158368871/500000000 : ℝ)*X 1 1+(6394732717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((2412061523/5000000000 : ℝ)*X 0 0+(4827400973/10000000000 : ℝ)*X 0 1+(3262448353/10000000000 : ℝ)*X 0 2+(2412061523/5000000000 : ℝ)*X 1 0+(4827400973/10000000000 : ℝ)*X 1 1+(3262448353/10000000000 : ℝ)*X 1 2+(2412061523/5000000000 : ℝ)*X 2 0+(4827400973/10000000000 : ℝ)*X 2 1+(3262448353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-2446857217/10000000000 : ℝ)*X 0 0+(1981055049/10000000000 : ℝ)*X 0 1+(390058851/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2444008979/10000000000 : ℝ)*X 1 0+(-1978749023/10000000000 : ℝ)*X 1 1+(3902334603/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4018671079/10000000000 : ℝ)*X 2 0+(1898685231/2500000000 : ℝ)*X 2 1+(439/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((1823048973/5000000000 : ℝ)*X 0 0+(1722657113/2500000000 : ℝ)*X 0 1+(990054643/5000000000 : ℝ)*X 0 2+(1823048973/5000000000 : ℝ)*X 1 0+(1722657113/2500000000 : ℝ)*X 1 1+(990054643/5000000000 : ℝ)*X 1 2+(1823048973/5000000000 : ℝ)*X 2 0+(1722657113/2500000000 : ℝ)*X 2 1+(990054643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-991967091/5000000000 : ℝ)*X 0 0+(2443885581/10000000000 : ℝ)*X 0 1+(1560273651/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((1981624473/10000000000 : ℝ)*X 1 0+(-1220520197/5000000000 : ℝ)*X 1 1+(7804860623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((7591434891/10000000000 : ℝ)*X 2 0+(2011349549/5000000000 : ℝ)*X 2 1+(1749/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_18 : ((6887673283/10000000000 : ℝ)*X 0 0+(364977603/1000000000 : ℝ)*X 0 1+(1980015521/10000000000 : ℝ)*X 0 2+(6887673283/10000000000 : ℝ)*X 1 0+(364977603/1000000000 : ℝ)*X 1 1+(1980015521/10000000000 : ℝ)*X 1 2+(6887673283/10000000000 : ℝ)*X 2 0+(364977603/1000000000 : ℝ)*X 2 1+(1980015521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s2_s2_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((-921230579/2000000000 : ℝ)*X 0 0+(396710071/2000000000 : ℝ)*X 0 1+(3026888989/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s2_s2_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((992460929/5000000000 : ℝ)*X 1 0+(-2300889343/5000000000 : ℝ)*X 1 1+(6056825467/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s2_s2_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((6188240281/10000000000 : ℝ)*X 2 0+(1117058477/2000000000 : ℝ)*X 2 1+(44157561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s2_s2_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((1986048647/5000000000 : ℝ)*X 0 0+(1117058477/2000000000 : ℝ)*X 0 1+(830169867/2500000000 : ℝ)*X 0 2+(1986048647/5000000000 : ℝ)*X 1 0+(1117058477/2000000000 : ℝ)*X 1 1+(830169867/2500000000 : ℝ)*X 1 2+(1986048647/5000000000 : ℝ)*X 2 0+(1117058477/2000000000 : ℝ)*X 2 1+(830169867/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((9277/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9277/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6314914138715547746541/650442578125000000000000000 : ℝ) := by norm_num
    linear_combination (741830473023/1000000000000 : ℝ)*(base7) + (350934047399/1000000000000 : ℝ)*(base59) + (28229358003/250000000000 : ℝ)*(base60) + (300517735707/125000000000 : ℝ)*(major_s2_0) + (300517735707/125000000000 : ℝ)*(major_s2_1) + (300517735707/125000000000 : ℝ)*(major_s2_2) + (5722069/1000000000000 : ℝ)*(sp_s2_0) + (1686917/250000000000 : ℝ)*(sp_s2_1) + (1394553454589/500000000000 : ℝ)*(sp_s2_7) + (2789030100501/1000000000000 : ℝ)*(sp_s2_8) + (2789112631247/1000000000000 : ℝ)*(sp_s2_9) + (1150533307207/500000000000 : ℝ)*(sp_s2_12) + (37891539/500000000000 : ℝ)*(sp_s2_14) + (11705791/1000000000000 : ℝ)*(sp_s2_25) + (779623923591/500000000000 : ℝ)*(f.failure) + (2789112631247/1000000000000 : ℝ)*(f.sum) + (34280743037987717/49835500000000000000000000000 : ℝ)*base63 + (3976171488471/4100000000000000000000000 : ℝ)*base64 + (43659641185073/89375000000000000000000000 : ℝ)*base66 + (1112815431511/4356250000000000000000000 : ℝ)*base69 + (1040845748809997/1958980000000000000000000000 : ℝ)*base70 + (53472506803923/119450000000000000000000000 : ℝ)*base72 + (22190602255559/71500000000000000000000000 : ℝ)*base74 + (47605190105833/119450000000000000000000000 : ℝ)*base76 + (14795245779946553/213516875000000000000000000000 : ℝ)*base79 + (963/25000000000000000 : ℝ)*base87 + (963/25000000000000000 : ℝ)*base89 + (963/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37091/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37091/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (365173538376218762078359487/59528504750000000000000000000000 : ℝ) := by norm_num
    linear_combination (29670007087/40000000000 : ℝ)*(base7) + (438011/1000000000000 : ℝ)*(base40) + (70120800927/200000000000 : ℝ)*(base59) + (118999351199/500000000000 : ℝ)*(base60) + (2403515648607/1000000000000 : ℝ)*(major_s2_0) + (2403515648607/1000000000000 : ℝ)*(major_s2_1) + (2403515648607/1000000000000 : ℝ)*(major_s2_2) + (4305927/1000000000000 : ℝ)*(sp_s2_1) + (2676801/1000000000000 : ℝ)*(sp_s2_6) + (25243619/500000000000 : ℝ)*(sp_s2_8) + (697079321813/250000000000 : ℝ)*(sp_s2_13) + (2788262494087/1000000000000 : ℝ)*(sp_s2_14) + (697079321813/250000000000 : ℝ)*(sp_s2_15) + (1150294595337/500000000000 : ℝ)*(sp_s2_18) + (1558841690301/1000000000000 : ℝ)*(f.failure) + (697079321813/250000000000 : ℝ)*(f.sum) + (2171167913139893119/2790788000000000000000000000000 : ℝ)*base63 + (100353141542613/229600000000000000000000000 : ℝ)*base65 + (299094238492779/1430000000000000000000000000 : ℝ)*base67 + (1587448594676541/1951600000000000000000000000 : ℝ)*base69 + (209003877363057683/329108640000000000000000000000 : ℝ)*base71 + (12086254348363/955600000000000000000000000 : ℝ)*base72 + (258015620761791/572000000000000000000000000 : ℝ)*base75 + (883884920032583/1433400000000000000000000000 : ℝ)*base77 + (119463462628327847/1708135000000000000000000000000 : ℝ)*base78 + (24993/50000000000000000 : ℝ)*base87 + (24993/50000000000000000 : ℝ)*base89 + (24993/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1321/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1321/6250 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (42691815667297685911538007/7003353500000000000000000000000 : ℝ) := by norm_num
    linear_combination (263368786131/1000000000000 : ℝ)*(base5) + (7088228933/100000000000 : ℝ)*(base7) + (2583277/250000000000 : ℝ)*(base8) + (2581/250000000 : ℝ)*(base16) + (721/200000000000 : ℝ)*(base50) + (103089789941/125000000000 : ℝ)*(base59) + (395753278431/200000000000 : ℝ)*(major_s2_0) + (395753278431/200000000000 : ℝ)*(major_s2_1) + (395753278431/200000000000 : ℝ)*(major_s2_2) + (1607/1000000000000 : ℝ)*(sp_s2_6) + (2630211611911/1000000000000 : ℝ)*(sp_s2_19) + (2630211621019/1000000000000 : ℝ)*(sp_s2_20) + (57871814623/20000000000 : ℝ)*(sp_s2_21) + (272719176793/250000000000 : ℝ)*(sp_s2_25) + (64168160279/50000000000 : ℝ)*(f.failure) + (2630221945019/1000000000000 : ℝ)*(f.sum) + (7432339940163161/79736800000000000000000000000 : ℝ)*base63 + (966827590931/6560000000000000000000000 : ℝ)*base65 + (112174825503493/286000000000000000000000000 : ℝ)*base66 + (3410630214493/55760000000000000000000000 : ℝ)*base68 + (21186296968596521/47015520000000000000000000000 : ℝ)*base71 + (5058040116659/191120000000000000000000000 : ℝ)*base72 + (3209210176703/114400000000000000000000000 : ℝ)*base75 + (24505659369689/286680000000000000000000000 : ℝ)*base76 + (61094517053260751/341627000000000000000000000000 : ℝ)*base78 + (1447/2500000000000000 : ℝ)*base87 + (1447/2500000000000000 : ℝ)*base89 + (1447/2500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((21501/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21501/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(429/500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(429/500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4879/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4879/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9277/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9277/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37091/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37091/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1321/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1321/6250 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306057_s2 p hpa hpb X hX hprev1

#print axioms solution

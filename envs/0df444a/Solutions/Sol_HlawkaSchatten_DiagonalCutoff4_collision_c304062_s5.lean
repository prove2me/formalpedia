-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304062_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:48:32.551357+00:00
-- url     : https://prove2.me/submissions/7027bdad-4399-4c2f-967d-3036fb877c8f

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
theorem collision_support_c304062_s5_s5_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2303109677/10000000000 : ℝ)*x 0 + (4871654991/10000000000 : ℝ)*x 1 + (-87705273/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2303109677/10000000000 : ℝ)^133 ≤ (14463576196511/100000000000000 : ℝ)^101 := by
    have hnat : (2303109677 : ℕ)^133*100000000000000^101 ≤ 14463576196511^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2303109677 10000000000 14463576196511 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4871654991/10000000000 : ℝ)^133 ≤ (38790247585273/100000000000000 : ℝ)^101 := by
    have hnat : (4871654991 : ℕ)^133*100000000000000^101 ≤ 38790247585273^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4871654991 10000000000 38790247585273 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87705273/156250000 : ℝ)^133 ≤ (46746176204667/100000000000000 : ℝ)^101 := by
    have hnat : (87705273 : ℕ)^133*100000000000000^101 ≤ 46746176204667^101*156250000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87705273 156250000 46746176204667 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2303109677/10000000000 : ℝ), (4871654991/10000000000 : ℝ), (-87705273/156250000 : ℝ)] ![(14463576196511/100000000000000 : ℝ), (38790247585273/100000000000000 : ℝ), (46746176204667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2303109677/10000000000 : ℝ)|^133 ≤ (14463576196511/100000000000000 : ℝ)^101
        have hw : |(-2303109677/10000000000 : ℝ)|=(2303109677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4871654991/10000000000 : ℝ)|^133 ≤ (38790247585273/100000000000000 : ℝ)^101
        have hw : |(4871654991/10000000000 : ℝ)|=(4871654991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-87705273/156250000 : ℝ)|^133 ≤ (46746176204667/100000000000000 : ℝ)^101
        have hw : |(-87705273/156250000 : ℝ)|=(87705273/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s5_s5_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (973927413/2000000000 : ℝ)*x 0 + (-1153398107/5000000000 : ℝ)*x 1 + (-1122457201/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (973927413/2000000000 : ℝ)^133 ≤ (19384545318379/50000000000000 : ℝ)^101 := by
    have hnat : (973927413 : ℕ)^133*50000000000000^101 ≤ 19384545318379^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973927413 2000000000 19384545318379 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1153398107/5000000000 : ℝ)^133 ≤ (579762823609/4000000000000 : ℝ)^101 := by
    have hnat : (1153398107 : ℕ)^133*4000000000000^101 ≤ 579762823609^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153398107 5000000000 579762823609 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122457201/2000000000 : ℝ)^133 ≤ (46736838759503/100000000000000 : ℝ)^101 := by
    have hnat : (1122457201 : ℕ)^133*100000000000000^101 ≤ 46736838759503^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122457201 2000000000 46736838759503 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(973927413/2000000000 : ℝ), (-1153398107/5000000000 : ℝ), (-1122457201/2000000000 : ℝ)] ![(19384545318379/50000000000000 : ℝ), (579762823609/4000000000000 : ℝ), (46736838759503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(973927413/2000000000 : ℝ)|^133 ≤ (19384545318379/50000000000000 : ℝ)^101
        have hw : |(973927413/2000000000 : ℝ)|=(973927413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1153398107/5000000000 : ℝ)|^133 ≤ (579762823609/4000000000000 : ℝ)^101
        have hw : |(-1153398107/5000000000 : ℝ)|=(1153398107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1122457201/2000000000 : ℝ)|^133 ≤ (46736838759503/100000000000000 : ℝ)^101
        have hw : |(-1122457201/2000000000 : ℝ)|=(1122457201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s5_s5_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5425756779/10000000000 : ℝ)*x 0 + (2709654773/5000000000 : ℝ)*x 1 + (-114217123/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5425756779/10000000000 : ℝ)^133 ≤ (5587775529981/12500000000000 : ℝ)^101 := by
    have hnat : (5425756779 : ℕ)^133*12500000000000^101 ≤ 5587775529981^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425756779 10000000000 5587775529981 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709654773/5000000000 : ℝ)^133 ≤ (8926453980367/20000000000000 : ℝ)^101 := by
    have hnat : (2709654773 : ℕ)^133*20000000000000^101 ≤ 8926453980367^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709654773 5000000000 8926453980367 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114217123/625000000 : ℝ)^133 ≤ (5332762920319/50000000000000 : ℝ)^101 := by
    have hnat : (114217123 : ℕ)^133*50000000000000^101 ≤ 5332762920319^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114217123 625000000 5332762920319 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5425756779/10000000000 : ℝ), (2709654773/5000000000 : ℝ), (-114217123/625000000 : ℝ)] ![(5587775529981/12500000000000 : ℝ), (8926453980367/20000000000000 : ℝ), (5332762920319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5425756779/10000000000 : ℝ)|^133 ≤ (5587775529981/12500000000000 : ℝ)^101
        have hw : |(5425756779/10000000000 : ℝ)|=(5425756779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709654773/5000000000 : ℝ)|^133 ≤ (8926453980367/20000000000000 : ℝ)^101
        have hw : |(2709654773/5000000000 : ℝ)|=(2709654773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-114217123/625000000 : ℝ)|^133 ≤ (5332762920319/50000000000000 : ℝ)^101
        have hw : |(-114217123/625000000 : ℝ)|=(114217123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s5_s5_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134669591/10000000000 : ℝ)*x 0 + (114753387/250000000 : ℝ)*x 1 + (-3000570007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134669591/10000000000 : ℝ)^133 ≤ (13087038159431/100000000000000 : ℝ)^101 := by
    have hnat : (2134669591 : ℕ)^133*100000000000000^101 ≤ 13087038159431^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134669591 10000000000 13087038159431 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114753387/250000000 : ℝ)^133 ≤ (17932924239333/50000000000000 : ℝ)^101 := by
    have hnat : (114753387 : ℕ)^133*50000000000000^101 ≤ 17932924239333^101*250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114753387 250000000 17932924239333 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3000570007/5000000000 : ℝ)^133 ≤ (25523556672359/50000000000000 : ℝ)^101 := by
    have hnat : (3000570007 : ℕ)^133*50000000000000^101 ≤ 25523556672359^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3000570007 5000000000 25523556672359 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134669591/10000000000 : ℝ), (114753387/250000000 : ℝ), (-3000570007/5000000000 : ℝ)] ![(13087038159431/100000000000000 : ℝ), (17932924239333/50000000000000 : ℝ), (25523556672359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134669591/10000000000 : ℝ)|^133 ≤ (13087038159431/100000000000000 : ℝ)^101
        have hw : |(-2134669591/10000000000 : ℝ)|=(2134669591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(114753387/250000000 : ℝ)|^133 ≤ (17932924239333/50000000000000 : ℝ)^101
        have hw : |(114753387/250000000 : ℝ)|=(114753387/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3000570007/5000000000 : ℝ)|^133 ≤ (25523556672359/50000000000000 : ℝ)^101
        have hw : |(-3000570007/5000000000 : ℝ)|=(3000570007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s5_s5_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (303454759/625000000 : ℝ)*x 0 + (-478793913/2500000000 : ℝ)*x 1 + (-147768151/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (303454759/625000000 : ℝ)^133 ≤ (9654650950927/25000000000000 : ℝ)^101 := by
    have hnat : (303454759 : ℕ)^133*25000000000000^101 ≤ 9654650950927^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303454759 625000000 9654650950927 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478793913/2500000000 : ℝ)^133 ≤ (5672304838769/50000000000000 : ℝ)^101 := by
    have hnat : (478793913 : ℕ)^133*50000000000000^101 ≤ 5672304838769^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478793913 2500000000 5672304838769 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147768151/250000000 : ℝ)^133 ≤ (50036786503381/100000000000000 : ℝ)^101 := by
    have hnat : (147768151 : ℕ)^133*100000000000000^101 ≤ 50036786503381^101*250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147768151 250000000 50036786503381 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(303454759/625000000 : ℝ), (-478793913/2500000000 : ℝ), (-147768151/250000000 : ℝ)] ![(9654650950927/25000000000000 : ℝ), (5672304838769/50000000000000 : ℝ), (50036786503381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(303454759/625000000 : ℝ)|^133 ≤ (9654650950927/25000000000000 : ℝ)^101
        have hw : |(303454759/625000000 : ℝ)|=(303454759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-478793913/2500000000 : ℝ)|^133 ≤ (5672304838769/50000000000000 : ℝ)^101
        have hw : |(-478793913/2500000000 : ℝ)|=(478793913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147768151/250000000 : ℝ)|^133 ≤ (50036786503381/100000000000000 : ℝ)^101
        have hw : |(-147768151/250000000 : ℝ)|=(147768151/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s5_s5_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (495104879/1000000000 : ℝ)*x 0 + (5553600131/10000000000 : ℝ)*x 1 + (285121703/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (495104879/1000000000 : ℝ)^133 ≤ (9906211971361/25000000000000 : ℝ)^101 := by
    have hnat : (495104879 : ℕ)^133*25000000000000^101 ≤ 9906211971361^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495104879 1000000000 9906211971361 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5553600131/10000000000 : ℝ)^133 ≤ (46094355742083/100000000000000 : ℝ)^101 := by
    have hnat : (5553600131 : ℕ)^133*100000000000000^101 ≤ 46094355742083^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5553600131 10000000000 46094355742083 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285121703/1250000000 : ℝ)^133 ≤ (892549771901/6250000000000 : ℝ)^101 := by
    have hnat : (285121703 : ℕ)^133*6250000000000^101 ≤ 892549771901^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285121703 1250000000 892549771901 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(495104879/1000000000 : ℝ), (5553600131/10000000000 : ℝ), (285121703/1250000000 : ℝ)] ![(9906211971361/25000000000000 : ℝ), (46094355742083/100000000000000 : ℝ), (892549771901/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(495104879/1000000000 : ℝ)|^133 ≤ (9906211971361/25000000000000 : ℝ)^101
        have hw : |(495104879/1000000000 : ℝ)|=(495104879/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5553600131/10000000000 : ℝ)|^133 ≤ (46094355742083/100000000000000 : ℝ)^101
        have hw : |(5553600131/10000000000 : ℝ)|=(5553600131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(285121703/1250000000 : ℝ)|^133 ≤ (892549771901/6250000000000 : ℝ)^101
        have hw : |(285121703/1250000000 : ℝ)|=(285121703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s5_s5_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1317243737/2500000000 : ℝ)*x 0 + (581332963/1000000000 : ℝ)*x 1 + (-368528229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317243737/2500000000 : ℝ)^133 ≤ (43009080345237/100000000000000 : ℝ)^101 := by
    have hnat : (1317243737 : ℕ)^133*100000000000000^101 ≤ 43009080345237^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317243737 2500000000 43009080345237 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (581332963/1000000000 : ℝ)^133 ≤ (9790780292983/20000000000000 : ℝ)^101 := by
    have hnat : (581332963 : ℕ)^133*20000000000000^101 ≤ 9790780292983^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      581332963 1000000000 9790780292983 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (368528229/2500000000 : ℝ)^133 ≤ (8037018165301/100000000000000 : ℝ)^101 := by
    have hnat : (368528229 : ℕ)^133*100000000000000^101 ≤ 8037018165301^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368528229 2500000000 8037018165301 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317243737/2500000000 : ℝ), (581332963/1000000000 : ℝ), (-368528229/2500000000 : ℝ)] ![(43009080345237/100000000000000 : ℝ), (9790780292983/20000000000000 : ℝ), (8037018165301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317243737/2500000000 : ℝ)|^133 ≤ (43009080345237/100000000000000 : ℝ)^101
        have hw : |(1317243737/2500000000 : ℝ)|=(1317243737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(581332963/1000000000 : ℝ)|^133 ≤ (9790780292983/20000000000000 : ℝ)^101
        have hw : |(581332963/1000000000 : ℝ)|=(581332963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-368528229/2500000000 : ℝ)|^133 ≤ (8037018165301/100000000000000 : ℝ)^101
        have hw : |(-368528229/2500000000 : ℝ)|=(368528229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s5_s5_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-187405913/1000000000 : ℝ)*x 0 + (2407895411/5000000000 : ℝ)*x 1 + (-2988167489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (187405913/1000000000 : ℝ)^133 ≤ (2756246173167/25000000000000 : ℝ)^101 := by
    have hnat : (187405913 : ℕ)^133*25000000000000^101 ≤ 2756246173167^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187405913 1000000000 2756246173167 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2407895411/5000000000 : ℝ)^133 ≤ (19102784011069/50000000000000 : ℝ)^101 := by
    have hnat : (2407895411 : ℕ)^133*50000000000000^101 ≤ 19102784011069^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2407895411 5000000000 19102784011069 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2988167489/5000000000 : ℝ)^133 ≤ (50769447268789/100000000000000 : ℝ)^101 := by
    have hnat : (2988167489 : ℕ)^133*100000000000000^101 ≤ 50769447268789^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2988167489 5000000000 50769447268789 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-187405913/1000000000 : ℝ), (2407895411/5000000000 : ℝ), (-2988167489/5000000000 : ℝ)] ![(2756246173167/25000000000000 : ℝ), (19102784011069/50000000000000 : ℝ), (50769447268789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-187405913/1000000000 : ℝ)|^133 ≤ (2756246173167/25000000000000 : ℝ)^101
        have hw : |(-187405913/1000000000 : ℝ)|=(187405913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2407895411/5000000000 : ℝ)|^133 ≤ (19102784011069/50000000000000 : ℝ)^101
        have hw : |(2407895411/5000000000 : ℝ)|=(2407895411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2988167489/5000000000 : ℝ)|^133 ≤ (50769447268789/100000000000000 : ℝ)^101
        have hw : |(-2988167489/5000000000 : ℝ)|=(2988167489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s5_s5_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1158480187/2500000000 : ℝ)*x 0 + (-436294471/2000000000 : ℝ)*x 1 + (-5926864149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1158480187/2500000000 : ℝ)^133 ≤ (18158523800379/50000000000000 : ℝ)^101 := by
    have hnat : (1158480187 : ℕ)^133*50000000000000^101 ≤ 18158523800379^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158480187 2500000000 18158523800379 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436294471/2000000000 : ℝ)^133 ≤ (13466187974793/100000000000000 : ℝ)^101 := by
    have hnat : (436294471 : ℕ)^133*100000000000000^101 ≤ 13466187974793^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436294471 2000000000 13466187974793 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5926864149/10000000000 : ℝ)^133 ≤ (6277095550273/12500000000000 : ℝ)^101 := by
    have hnat : (5926864149 : ℕ)^133*12500000000000^101 ≤ 6277095550273^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5926864149 10000000000 6277095550273 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1158480187/2500000000 : ℝ), (-436294471/2000000000 : ℝ), (-5926864149/10000000000 : ℝ)] ![(18158523800379/50000000000000 : ℝ), (13466187974793/100000000000000 : ℝ), (6277095550273/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1158480187/2500000000 : ℝ)|^133 ≤ (18158523800379/50000000000000 : ℝ)^101
        have hw : |(1158480187/2500000000 : ℝ)|=(1158480187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436294471/2000000000 : ℝ)|^133 ≤ (13466187974793/100000000000000 : ℝ)^101
        have hw : |(-436294471/2000000000 : ℝ)|=(436294471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5926864149/10000000000 : ℝ)|^133 ≤ (6277095550273/12500000000000 : ℝ)^101
        have hw : |(-5926864149/10000000000 : ℝ)|=(5926864149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s5_s5_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1374755089/2500000000 : ℝ)*x 0 + (2500771339/5000000000 : ℝ)*x 1 + (2288561233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1374755089/2500000000 : ℝ)^133 ≤ (9099750526429/20000000000000 : ℝ)^101 := by
    have hnat : (1374755089 : ℕ)^133*20000000000000^101 ≤ 9099750526429^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374755089 2500000000 9099750526429 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2500771339/5000000000 : ℝ)^133 ≤ (8031572459453/20000000000000 : ℝ)^101 := by
    have hnat : (2500771339 : ℕ)^133*20000000000000^101 ≤ 8031572459453^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2500771339 5000000000 8031572459453 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2288561233/10000000000 : ℝ)^133 ≤ (7171692530049/50000000000000 : ℝ)^101 := by
    have hnat : (2288561233 : ℕ)^133*50000000000000^101 ≤ 7171692530049^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288561233 10000000000 7171692530049 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1374755089/2500000000 : ℝ), (2500771339/5000000000 : ℝ), (2288561233/10000000000 : ℝ)] ![(9099750526429/20000000000000 : ℝ), (8031572459453/20000000000000 : ℝ), (7171692530049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1374755089/2500000000 : ℝ)|^133 ≤ (9099750526429/20000000000000 : ℝ)^101
        have hw : |(1374755089/2500000000 : ℝ)|=(1374755089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2500771339/5000000000 : ℝ)|^133 ≤ (8031572459453/20000000000000 : ℝ)^101
        have hw : |(2500771339/5000000000 : ℝ)|=(2500771339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2288561233/10000000000 : ℝ)|^133 ≤ (7171692530049/50000000000000 : ℝ)^101
        have hw : |(2288561233/10000000000 : ℝ)|=(2288561233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s5_s5_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5918888523/10000000000 : ℝ)*x 0 + (5157925909/10000000000 : ℝ)*x 1 + (-738153393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5918888523/10000000000 : ℝ)^133 ≤ (25063898984229/50000000000000 : ℝ)^101 := by
    have hnat : (5918888523 : ℕ)^133*50000000000000^101 ≤ 25063898984229^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5918888523 10000000000 25063898984229 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5157925909/10000000000 : ℝ)^133 ≤ (20909714621961/50000000000000 : ℝ)^101 := by
    have hnat : (5157925909 : ℕ)^133*50000000000000^101 ≤ 20909714621961^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5157925909 10000000000 20909714621961 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (738153393/5000000000 : ℝ)^133 ≤ (1610554555371/20000000000000 : ℝ)^101 := by
    have hnat : (738153393 : ℕ)^133*20000000000000^101 ≤ 1610554555371^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738153393 5000000000 1610554555371 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5918888523/10000000000 : ℝ), (5157925909/10000000000 : ℝ), (-738153393/5000000000 : ℝ)] ![(25063898984229/50000000000000 : ℝ), (20909714621961/50000000000000 : ℝ), (1610554555371/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5918888523/10000000000 : ℝ)|^133 ≤ (25063898984229/50000000000000 : ℝ)^101
        have hw : |(5918888523/10000000000 : ℝ)|=(5918888523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5157925909/10000000000 : ℝ)|^133 ≤ (20909714621961/50000000000000 : ℝ)^101
        have hw : |(5157925909/10000000000 : ℝ)|=(5157925909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-738153393/5000000000 : ℝ)|^133 ≤ (1610554555371/20000000000000 : ℝ)^101
        have hw : |(-738153393/5000000000 : ℝ)|=(738153393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s5_s5_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-218120599/1250000000 : ℝ)*x 0 + (203584719/400000000 : ℝ)*x 1 + (-725746543/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218120599/1250000000 : ℝ)^133 ≤ (401440009291/4000000000000 : ℝ)^101 := by
    have hnat : (218120599 : ℕ)^133*4000000000000^101 ≤ 401440009291^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218120599 1250000000 401440009291 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203584719/400000000 : ℝ)^133 ≤ (41091666924391/100000000000000 : ℝ)^101 := by
    have hnat : (203584719 : ℕ)^133*100000000000000^101 ≤ 41091666924391^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203584719 400000000 41091666924391 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (725746543/1250000000 : ℝ)^133 ≤ (48872332836289/100000000000000 : ℝ)^101 := by
    have hnat : (725746543 : ℕ)^133*100000000000000^101 ≤ 48872332836289^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      725746543 1250000000 48872332836289 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218120599/1250000000 : ℝ), (203584719/400000000 : ℝ), (-725746543/1250000000 : ℝ)] ![(401440009291/4000000000000 : ℝ), (41091666924391/100000000000000 : ℝ), (48872332836289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218120599/1250000000 : ℝ)|^133 ≤ (401440009291/4000000000000 : ℝ)^101
        have hw : |(-218120599/1250000000 : ℝ)|=(218120599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(203584719/400000000 : ℝ)|^133 ≤ (41091666924391/100000000000000 : ℝ)^101
        have hw : |(203584719/400000000 : ℝ)|=(203584719/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-725746543/1250000000 : ℝ)|^133 ≤ (48872332836289/100000000000000 : ℝ)^101
        have hw : |(-725746543/1250000000 : ℝ)|=(725746543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s5_s5_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (135944717/250000000 : ℝ)*x 0 + (-262356839/1250000000 : ℝ)*x 1 + (-13023191/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135944717/250000000 : ℝ)^133 ≤ (22416393462657/50000000000000 : ℝ)^101 := by
    have hnat : (135944717 : ℕ)^133*50000000000000^101 ≤ 22416393462657^101*250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135944717 250000000 22416393462657 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262356839/1250000000 : ℝ)^133 ≤ (255973441527/2000000000000 : ℝ)^101 := by
    have hnat : (262356839 : ℕ)^133*2000000000000^101 ≤ 255973441527^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262356839 1250000000 255973441527 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13023191/25000000 : ℝ)^133 ≤ (21184270489977/50000000000000 : ℝ)^101 := by
    have hnat : (13023191 : ℕ)^133*50000000000000^101 ≤ 21184270489977^101*25000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13023191 25000000 21184270489977 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135944717/250000000 : ℝ), (-262356839/1250000000 : ℝ), (-13023191/25000000 : ℝ)] ![(22416393462657/50000000000000 : ℝ), (255973441527/2000000000000 : ℝ), (21184270489977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135944717/250000000 : ℝ)|^133 ≤ (22416393462657/50000000000000 : ℝ)^101
        have hw : |(135944717/250000000 : ℝ)|=(135944717/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-262356839/1250000000 : ℝ)|^133 ≤ (255973441527/2000000000000 : ℝ)^101
        have hw : |(-262356839/1250000000 : ℝ)|=(262356839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13023191/25000000 : ℝ)|^133 ≤ (21184270489977/50000000000000 : ℝ)^101
        have hw : |(-13023191/25000000 : ℝ)|=(13023191/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s5_s5_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (599056711/1250000000 : ℝ)*x 0 + (527536887/1000000000 : ℝ)*x 1 + (565751127/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (599056711/1250000000 : ℝ)^133 ≤ (37961953631851/100000000000000 : ℝ)^101 := by
    have hnat : (599056711 : ℕ)^133*100000000000000^101 ≤ 37961953631851^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599056711 1250000000 37961953631851 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527536887/1000000000 : ℝ)^133 ≤ (2692363826509/6250000000000 : ℝ)^101 := by
    have hnat : (527536887 : ℕ)^133*6250000000000^101 ≤ 2692363826509^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527536887 1000000000 2692363826509 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565751127/2000000000 : ℝ)^133 ≤ (4740056282829/25000000000000 : ℝ)^101 := by
    have hnat : (565751127 : ℕ)^133*25000000000000^101 ≤ 4740056282829^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565751127 2000000000 4740056282829 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(599056711/1250000000 : ℝ), (527536887/1000000000 : ℝ), (565751127/2000000000 : ℝ)] ![(37961953631851/100000000000000 : ℝ), (2692363826509/6250000000000 : ℝ), (4740056282829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(599056711/1250000000 : ℝ)|^133 ≤ (37961953631851/100000000000000 : ℝ)^101
        have hw : |(599056711/1250000000 : ℝ)|=(599056711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527536887/1000000000 : ℝ)|^133 ≤ (2692363826509/6250000000000 : ℝ)^101
        have hw : |(527536887/1000000000 : ℝ)|=(527536887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565751127/2000000000 : ℝ)|^133 ≤ (4740056282829/25000000000000 : ℝ)^101
        have hw : |(565751127/2000000000 : ℝ)|=(565751127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304062_s5_s5_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5983534421/10000000000 : ℝ)*x 0 + (4989925899/10000000000 : ℝ)*x 1 + (-324390221/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5983534421/10000000000 : ℝ)^133 ≤ (50849999860281/100000000000000 : ℝ)^101 := by
    have hnat : (5983534421 : ℕ)^133*100000000000000^101 ≤ 50849999860281^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5983534421 10000000000 50849999860281 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4989925899/10000000000 : ℝ)^133 ≤ (40035083692979/100000000000000 : ℝ)^101 := by
    have hnat : (4989925899 : ℕ)^133*100000000000000^101 ≤ 40035083692979^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4989925899 10000000000 40035083692979 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324390221/2000000000 : ℝ)^133 ≤ (2278729107179/25000000000000 : ℝ)^101 := by
    have hnat : (324390221 : ℕ)^133*25000000000000^101 ≤ 2278729107179^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324390221 2000000000 2278729107179 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5983534421/10000000000 : ℝ), (4989925899/10000000000 : ℝ), (-324390221/2000000000 : ℝ)] ![(50849999860281/100000000000000 : ℝ), (40035083692979/100000000000000 : ℝ), (2278729107179/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5983534421/10000000000 : ℝ)|^133 ≤ (50849999860281/100000000000000 : ℝ)^101
        have hw : |(5983534421/10000000000 : ℝ)|=(5983534421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4989925899/10000000000 : ℝ)|^133 ≤ (40035083692979/100000000000000 : ℝ)^101
        have hw : |(4989925899/10000000000 : ℝ)|=(4989925899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-324390221/2000000000 : ℝ)|^133 ≤ (2278729107179/25000000000000 : ℝ)^101
        have hw : |(-324390221/2000000000 : ℝ)|=(324390221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304062_s5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev4 : (0 : ℝ) ≤ ((27493/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27493/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55371/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(55371/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9447/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-9447/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((882/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(882/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28337/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28337/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8261/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8261/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (27493/50000 : ℝ) ^ (33/8 : ℝ) ≤ (5301759756444879/62500000000000000 : ℝ) := by
    have hpowers : (27493/50000 : ℝ)^33 ≤ (5301759756444879/62500000000000000 : ℝ)^8 := by
      have hnat : (27493 : ℕ)^33*62500000000000000^8 ≤ 5301759756444879^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27493 50000 5301759756444879 62500000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27493/50000 : ℝ)) (X := (5301759756444879/62500000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner0a : (67801759756444879/62500000000000000 : ℝ) ≤ (1019934661604991/1000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (67801759756444879/62500000000000000 : ℝ)^8 ≤ (1019934661604991/1000000000000000 : ℝ)^33 := by
      have hnat : (67801759756444879 : ℕ)^8*1000000000000000^33 ≤ 1019934661604991^33*62500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67801759756444879 62500000000000000 1019934661604991 1000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1019934661604991/1000000000000000 : ℝ)) (X := (67801759756444879/62500000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner0b : (36551759756444879/31250000000000000 : ℝ) ≤ (2596802872881647/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (36551759756444879/31250000000000000 : ℝ)^8 ≤ (2596802872881647/2500000000000000 : ℝ)^33 := by
      have hnat : (36551759756444879 : ℕ)^8*2500000000000000^33 ≤ 2596802872881647^33*31250000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36551759756444879 31250000000000000 2596802872881647 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2596802872881647/2500000000000000 : ℝ)) (X := (36551759756444879/31250000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(19934661604991/549860000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(93932437738339/2749300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (27493/50000 : ℝ)) (alpha := (19934661604991/549860000000000 : ℝ)) (beta := (93932437738339/2749300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (27493/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(19934661604991/549860000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(93932437738339/2749300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (55371/100000 : ℝ) ^ (33/8 : ℝ) ≤ (17461026010874553/200000000000000000 : ℝ) := by
    have hpowers : (55371/100000 : ℝ)^33 ≤ (17461026010874553/200000000000000000 : ℝ)^8 := by
      have hnat : (55371 : ℕ)^33*200000000000000000^8 ≤ 17461026010874553^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55371 100000 17461026010874553 200000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (55371/100000 : ℝ)) (X := (17461026010874553/200000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner1a : (217461026010874553/200000000000000000 : ℝ) ≤ (10204987324012469/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (217461026010874553/200000000000000000 : ℝ)^8 ≤ (10204987324012469/10000000000000000 : ℝ)^33 := by
      have hnat : (217461026010874553 : ℕ)^8*10000000000000000^33 ≤ 10204987324012469^33*200000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        217461026010874553 200000000000000000 10204987324012469 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10204987324012469/10000000000000000 : ℝ)) (X := (217461026010874553/200000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner1b : (117461026010874553/100000000000000000 : ℝ) ≤ (5198929801758903/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (117461026010874553/100000000000000000 : ℝ)^8 ≤ (5198929801758903/5000000000000000 : ℝ)^33 := by
      have hnat : (117461026010874553 : ℕ)^8*5000000000000000^33 ≤ 5198929801758903^33*100000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        117461026010874553 100000000000000000 5198929801758903 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5198929801758903/5000000000000000 : ℝ)) (X := (117461026010874553/100000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(204987324012469/5537100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(192872279505337/5537100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (55371/100000 : ℝ)) (alpha := (204987324012469/5537100000000000 : ℝ)) (beta := (192872279505337/5537100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (55371/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(204987324012469/5537100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(192872279505337/5537100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (9447/25000 : ℝ) ^ (33/8 : ℝ) ≤ (1805447503445333017/100000000000000000000 : ℝ) := by
    have hpowers : (9447/25000 : ℝ)^33 ≤ (1805447503445333017/100000000000000000000 : ℝ)^8 := by
      have hnat : (9447 : ℕ)^33*100000000000000000000^8 ≤ 1805447503445333017^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9447 25000 1805447503445333017 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9447/25000 : ℝ)) (X := (1805447503445333017/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner2a : (101805447503445333017/100000000000000000000 : ℝ) ≤ (5021736113647601/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (101805447503445333017/100000000000000000000 : ℝ)^8 ≤ (5021736113647601/5000000000000000 : ℝ)^33 := by
      have hnat : (101805447503445333017 : ℕ)^8*5000000000000000^33 ≤ 5021736113647601^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101805447503445333017 100000000000000000000 5021736113647601 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5021736113647601/5000000000000000 : ℝ)) (X := (101805447503445333017/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner2b : (51805447503445333017/50000000000000000000 : ℝ) ≤ (5043182133211467/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (51805447503445333017/50000000000000000000 : ℝ)^8 ≤ (5043182133211467/5000000000000000 : ℝ)^33 := by
      have hnat : (51805447503445333017 : ℕ)^8*5000000000000000^33 ≤ 5043182133211467^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51805447503445333017 50000000000000000000 5043182133211467 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5043182133211467/5000000000000000 : ℝ)) (X := (51805447503445333017/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(7245371215867/629800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(10723009781933/944700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (9447/25000 : ℝ)) (alpha := (7245371215867/629800000000000 : ℝ)) (beta := (10723009781933/944700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (9447/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(7245371215867/629800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(10723009781933/944700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-2303109677/10000000000 : ℝ)*X 0 0+(4871654991/10000000000 : ℝ)*X 0 1+(-87705273/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((973927413/2000000000 : ℝ)*X 1 0+(-1153398107/5000000000 : ℝ)*X 1 1+(-1122457201/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((5425756779/10000000000 : ℝ)*X 0 0+(2709654773/5000000000 : ℝ)*X 0 1+(-114217123/625000000 : ℝ)*X 0 2+(5425756779/10000000000 : ℝ)*X 1 0+(2709654773/5000000000 : ℝ)*X 1 1+(-114217123/625000000 : ℝ)*X 1 2+(5425756779/10000000000 : ℝ)*X 2 0+(2709654773/5000000000 : ℝ)*X 2 1+(-114217123/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-2134669591/10000000000 : ℝ)*X 0 0+(114753387/250000000 : ℝ)*X 0 1+(-3000570007/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((303454759/625000000 : ℝ)*X 1 0+(-478793913/2500000000 : ℝ)*X 1 1+(-147768151/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((495104879/1000000000 : ℝ)*X 2 0+(5553600131/10000000000 : ℝ)*X 2 1+(285121703/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((1317243737/2500000000 : ℝ)*X 0 0+(581332963/1000000000 : ℝ)*X 0 1+(-368528229/2500000000 : ℝ)*X 0 2+(1317243737/2500000000 : ℝ)*X 1 0+(581332963/1000000000 : ℝ)*X 1 1+(-368528229/2500000000 : ℝ)*X 1 2+(1317243737/2500000000 : ℝ)*X 2 0+(581332963/1000000000 : ℝ)*X 2 1+(-368528229/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-187405913/1000000000 : ℝ)*X 0 0+(2407895411/5000000000 : ℝ)*X 0 1+(-2988167489/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((1158480187/2500000000 : ℝ)*X 1 0+(-436294471/2000000000 : ℝ)*X 1 1+(-5926864149/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((1374755089/2500000000 : ℝ)*X 2 0+(2500771339/5000000000 : ℝ)*X 2 1+(2288561233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((5918888523/10000000000 : ℝ)*X 0 0+(5157925909/10000000000 : ℝ)*X 0 1+(-738153393/5000000000 : ℝ)*X 0 2+(5918888523/10000000000 : ℝ)*X 1 0+(5157925909/10000000000 : ℝ)*X 1 1+(-738153393/5000000000 : ℝ)*X 1 2+(5918888523/10000000000 : ℝ)*X 2 0+(5157925909/10000000000 : ℝ)*X 2 1+(-738153393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-218120599/1250000000 : ℝ)*X 0 0+(203584719/400000000 : ℝ)*X 0 1+(-725746543/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((135944717/250000000 : ℝ)*X 1 0+(-262356839/1250000000 : ℝ)*X 1 1+(-13023191/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((599056711/1250000000 : ℝ)*X 2 0+(527536887/1000000000 : ℝ)*X 2 1+(565751127/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((5983534421/10000000000 : ℝ)*X 0 0+(4989925899/10000000000 : ℝ)*X 0 1+(-324390221/2000000000 : ℝ)*X 0 2+(5983534421/10000000000 : ℝ)*X 1 0+(4989925899/10000000000 : ℝ)*X 1 1+(-324390221/2000000000 : ℝ)*X 1 2+(5983534421/10000000000 : ℝ)*X 2 0+(4989925899/10000000000 : ℝ)*X 2 1+(-324390221/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304062_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((882/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(882/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2938703572718098667006056495059/159792320984900000000000000000000000 : ℝ) := by norm_num
    linear_combination (208002427183/250000000000 : ℝ)*(base39) + (17309488191/25000000000 : ℝ)*(base49) + (138404663547/1000000000000 : ℝ)*(base60) + (10918296613391/1000000000000 : ℝ)*(major_s5_0) + (10918296613391/1000000000000 : ℝ)*(major_s5_1) + (10918296613391/1000000000000 : ℝ)*(major_s5_2) + (54502053/1000000000000 : ℝ)*(sp_s5_0) + (164240709/1000000000000 : ℝ)*(sp_s5_1) + (14637908844933/1000000000000 : ℝ)*(sp_s5_7) + (914849787763/62500000000 : ℝ)*(sp_s5_8) + (14637693312697/1000000000000 : ℝ)*(sp_s5_9) + (1799655937383/250000000000 : ℝ)*(sp_s5_13) + (202502069/1000000000000 : ℝ)*(sp_s5_15) + (270034289/1000000000000 : ℝ)*(sp_s5_23) + (1799655937383/250000000000 : ℝ)*(f.failure) + (7318981673493/500000000000 : ℝ)*(f.sum) + (4730992497208391669/34872655800000000000000000000000 : ℝ)*base63 + (588916492816993/944700000000000000000000000 : ℝ)*base65 + (14104340254667/5537100000000000000000000000 : ℝ)*base67 + (370201618719697/629800000000000000000000000 : ℝ)*base69 + (608848762251643823/3246579637500000000000000000000 : ℝ)*base71 + (1013894898894511/2749300000000000000000000000 : ℝ)*base72 + (3312806630731799/5537100000000000000000000000 : ℝ)*base75 + (344219716818039/549860000000000000000000000 : ℝ)*base77 + (142858744708756517/237861703593750000000000000000 : ℝ)*base79 + (1289/1562500000000000 : ℝ)*base86 + (1289/1562500000000000 : ℝ)*base88 + (1289/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28337/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28337/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (328666864851442065111954367491/39948080246225000000000000000000000 : ℝ) := by norm_num
    linear_combination (816816375577/1000000000000 : ℝ)*(base39) + (18403282769/25000000000 : ℝ)*(base49) + (647621/1000000000000 : ℝ)*(base60) + (1381735876591/125000000000 : ℝ)*(major_s5_0) + (1381735876591/125000000000 : ℝ)*(major_s5_1) + (1381735876591/125000000000 : ℝ)*(major_s5_2) + (20397203/1000000000000 : ℝ)*(sp_s5_6) + (170869/1000000000000 : ℝ)*(sp_s5_7) + (27660483/1000000000000 : ℝ)*(sp_s5_8) + (14819750242933/1000000000000 : ℝ)*(sp_s5_14) + (370493068833/25000000000 : ℝ)*(sp_s5_15) + (7409875206901/500000000000 : ℝ)*(sp_s5_16) + (1457555601773/200000000000 : ℝ)*(sp_s5_20) + (27807891/125000000000 : ℝ)*(sp_s5_27) + (7288020869197/1000000000000 : ℝ)*(f.failure) + (7409875206901/500000000000 : ℝ)*(f.sum) + (706436535738136613/8718163950000000000000000000000 : ℝ)*base63 + (285257537757977/472350000000000000000000000 : ℝ)*base65 + (523330659716969/1384275000000000000000000000 : ℝ)*base67 + (43575916981773/78725000000000000000000000 : ℝ)*base68 + (12794150593497387311/12986318550000000000000000000000 : ℝ)*base71 + (547045491995103/687325000000000000000000000 : ℝ)*base73 + (103886707779857/346068750000000000000000000 : ℝ)*base75 + (63932510948881/274930000000000000000000000 : ℝ)*base77 + (707621944758342469/1902893628750000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (5923/12500000000000000 : ℝ)*base87 + (5923/12500000000000000 : ℝ)*base89 + (5923/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8261/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8261/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (102229498699941320643679628771/31958464196980000000000000000000000 : ℝ) := by norm_num
    linear_combination (1267342692239/1000000000000 : ℝ)*(base39) + (1037929/1000000000000 : ℝ)*(base40) + (273674128461/500000000000 : ℝ)*(base49) + (8925756531083/1000000000000 : ℝ)*(major_s5_0) + (8925756531083/1000000000000 : ℝ)*(major_s5_1) + (8925756531083/1000000000000 : ℝ)*(major_s5_2) + (3563423/125000000000 : ℝ)*(sp_s5_0) + (8134191/1000000000000 : ℝ)*(sp_s5_6) + (184273/5000000000 : ℝ)*(sp_s5_9) + (3865637/100000000000 : ℝ)*(sp_s5_20) + (11966576233979/1000000000000 : ℝ)*(sp_s5_21) + (5983302370681/500000000000 : ℝ)*(sp_s5_22) + (5983283943381/500000000000 : ℝ)*(sp_s5_23) + (1471215115991/250000000000 : ℝ)*(sp_s5_27) + (235396290181/40000000000 : ℝ)*(f.failure) + (5983302370681/500000000000 : ℝ)*(f.sum) + (1822546815477863717/34872655800000000000000000000000 : ℝ)*base63 + (310823952291431/944700000000000000000000000 : ℝ)*base64 + (1208340041381891/5537100000000000000000000000 : ℝ)*base67 + (121707137391021/629800000000000000000000000 : ℝ)*base69 + (3754482263558794601/12986318550000000000000000000000 : ℝ)*base71 + (2148774251769823/2749300000000000000000000000 : ℝ)*base72 + (966923006953637/5537100000000000000000000000 : ℝ)*base75 + (351049109534341/549860000000000000000000000 : ℝ)*base77 + (8161739853203425873/15223149030000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (79/500000000000000 : ℝ)*base87 + (79/500000000000000 : ℝ)*base89 + (79/500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev4 : (0 : ℝ) ≤ ((27493/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27493/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55371/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(55371/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9447/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-9447/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((882/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(882/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28337/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28337/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8261/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8261/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304062_s5 p hpa hpb X hX hprev4

#print axioms solution

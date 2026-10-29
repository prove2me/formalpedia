-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310045_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:24:44.996392+00:00
-- url     : https://prove2.me/submissions/76cd11aa-e569-4154-b376-62b2ac63bb6f

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
theorem collision_support_c310045_s1_s1_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5599777731/10000000000 : ℝ)*x 0 + (1669563849/5000000000 : ℝ)*x 1 + (932577749/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5599777731/10000000000 : ℝ)^9 ≤ (9489636599777/20000000000000 : ℝ)^7 := by
    have hnat : (5599777731 : ℕ)^9*20000000000000^7 ≤ 9489636599777^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5599777731 10000000000 9489636599777 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1669563849/5000000000 : ℝ)^9 ≤ (24407774312829/100000000000000 : ℝ)^7 := by
    have hnat : (1669563849 : ℕ)^9*100000000000000^7 ≤ 24407774312829^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669563849 5000000000 24407774312829 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (932577749/2500000000 : ℝ)^9 ≤ (2814404267083/10000000000000 : ℝ)^7 := by
    have hnat : (932577749 : ℕ)^9*10000000000000^7 ≤ 2814404267083^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932577749 2500000000 2814404267083 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5599777731/10000000000 : ℝ), (1669563849/5000000000 : ℝ), (932577749/2500000000 : ℝ)] ![(9489636599777/20000000000000 : ℝ), (24407774312829/100000000000000 : ℝ), (2814404267083/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5599777731/10000000000 : ℝ)|^9 ≤ (9489636599777/20000000000000 : ℝ)^7
        have hw : |(5599777731/10000000000 : ℝ)|=(5599777731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1669563849/5000000000 : ℝ)|^9 ≤ (24407774312829/100000000000000 : ℝ)^7
        have hw : |(1669563849/5000000000 : ℝ)|=(1669563849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(932577749/2500000000 : ℝ)|^9 ≤ (2814404267083/10000000000000 : ℝ)^7
        have hw : |(932577749/2500000000 : ℝ)|=(932577749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s1_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1369028043/2500000000 : ℝ)*x 0 + (-379755761/1250000000 : ℝ)*x 1 + (2075020567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1369028043/2500000000 : ℝ)^9 ≤ (46105224997139/100000000000000 : ℝ)^7 := by
    have hnat : (1369028043 : ℕ)^9*100000000000000^7 ≤ 46105224997139^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369028043 2500000000 46105224997139 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (379755761/1250000000 : ℝ)^9 ≤ (21615444684479/100000000000000 : ℝ)^7 := by
    have hnat : (379755761 : ℕ)^9*100000000000000^7 ≤ 21615444684479^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379755761 1250000000 21615444684479 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2075020567/5000000000 : ℝ)^9 ≤ (32279330312991/100000000000000 : ℝ)^7 := by
    have hnat : (2075020567 : ℕ)^9*100000000000000^7 ≤ 32279330312991^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075020567 5000000000 32279330312991 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1369028043/2500000000 : ℝ), (-379755761/1250000000 : ℝ), (2075020567/5000000000 : ℝ)] ![(46105224997139/100000000000000 : ℝ), (21615444684479/100000000000000 : ℝ), (32279330312991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1369028043/2500000000 : ℝ)|^9 ≤ (46105224997139/100000000000000 : ℝ)^7
        have hw : |(1369028043/2500000000 : ℝ)|=(1369028043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-379755761/1250000000 : ℝ)|^9 ≤ (21615444684479/100000000000000 : ℝ)^7
        have hw : |(-379755761/1250000000 : ℝ)|=(379755761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2075020567/5000000000 : ℝ)|^9 ≤ (32279330312991/100000000000000 : ℝ)^7
        have hw : |(2075020567/5000000000 : ℝ)|=(2075020567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s1_s1_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1591053/500000000 : ℝ)*x 0 + (-1940620073/2500000000 : ℝ)*x 1 + (1843915899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1591053/500000000 : ℝ)^9 ≤ (61546667169/100000000000000 : ℝ)^7 := by
    have hnat : (1591053 : ℕ)^9*100000000000000^7 ≤ 61546667169^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1591053 500000000 61546667169 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1940620073/2500000000 : ℝ)^9 ≤ (14441160030629/20000000000000 : ℝ)^7 := by
    have hnat : (1940620073 : ℕ)^9*20000000000000^7 ≤ 14441160030629^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940620073 2500000000 14441160030629 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1843915899/5000000000 : ℝ)^9 ≤ (27732653167757/100000000000000 : ℝ)^7 := by
    have hnat : (1843915899 : ℕ)^9*100000000000000^7 ≤ 27732653167757^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843915899 5000000000 27732653167757 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1591053/500000000 : ℝ), (-1940620073/2500000000 : ℝ), (1843915899/5000000000 : ℝ)] ![(61546667169/100000000000000 : ℝ), (14441160030629/20000000000000 : ℝ), (27732653167757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1591053/500000000 : ℝ)|^9 ≤ (61546667169/100000000000000 : ℝ)^7
        have hw : |(1591053/500000000 : ℝ)|=(1591053/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1940620073/2500000000 : ℝ)|^9 ≤ (14441160030629/20000000000000 : ℝ)^7
        have hw : |(-1940620073/2500000000 : ℝ)|=(1940620073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1843915899/5000000000 : ℝ)|^9 ≤ (27732653167757/100000000000000 : ℝ)^7
        have hw : |(1843915899/5000000000 : ℝ)|=(1843915899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s1_s1_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (36089359/80000000 : ℝ)*x 0 + (192315319/500000000 : ℝ)*x 1 + (879819619/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36089359/80000000 : ℝ)^9 ≤ (17967376408429/50000000000000 : ℝ)^7 := by
    have hnat : (36089359 : ℕ)^9*50000000000000^7 ≤ 17967376408429^7*80000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36089359 80000000 17967376408429 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192315319/500000000 : ℝ)^9 ≤ (29274196422341/100000000000000 : ℝ)^7 := by
    have hnat : (192315319 : ℕ)^9*100000000000000^7 ≤ 29274196422341^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192315319 500000000 29274196422341 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (879819619/2000000000 : ℝ)^9 ≤ (34791050745241/100000000000000 : ℝ)^7 := by
    have hnat : (879819619 : ℕ)^9*100000000000000^7 ≤ 34791050745241^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879819619 2000000000 34791050745241 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(36089359/80000000 : ℝ), (192315319/500000000 : ℝ), (879819619/2000000000 : ℝ)] ![(17967376408429/50000000000000 : ℝ), (29274196422341/100000000000000 : ℝ), (34791050745241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(36089359/80000000 : ℝ)|^9 ≤ (17967376408429/50000000000000 : ℝ)^7
        have hw : |(36089359/80000000 : ℝ)|=(36089359/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(192315319/500000000 : ℝ)|^9 ≤ (29274196422341/100000000000000 : ℝ)^7
        have hw : |(192315319/500000000 : ℝ)|=(192315319/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(879819619/2000000000 : ℝ)|^9 ≤ (34791050745241/100000000000000 : ℝ)^7
        have hw : |(879819619/2000000000 : ℝ)|=(879819619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s1_s1_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2829862909/5000000000 : ℝ)*x 0 + (-596374741/2000000000 : ℝ)*x 1 + (-400081863/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2829862909/5000000000 : ℝ)^9 ≤ (48102262581829/100000000000000 : ℝ)^7 := by
    have hnat : (2829862909 : ℕ)^9*100000000000000^7 ≤ 48102262581829^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829862909 5000000000 48102262581829 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (596374741/2000000000 : ℝ)^9 ≤ (10551478533233/50000000000000 : ℝ)^7 := by
    have hnat : (596374741 : ℕ)^9*50000000000000^7 ≤ 10551478533233^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596374741 2000000000 10551478533233 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400081863/1000000000 : ℝ)^9 ≤ (1539739017249/5000000000000 : ℝ)^7 := by
    have hnat : (400081863 : ℕ)^9*5000000000000^7 ≤ 1539739017249^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400081863 1000000000 1539739017249 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2829862909/5000000000 : ℝ), (-596374741/2000000000 : ℝ), (-400081863/1000000000 : ℝ)] ![(48102262581829/100000000000000 : ℝ), (10551478533233/50000000000000 : ℝ), (1539739017249/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2829862909/5000000000 : ℝ)|^9 ≤ (48102262581829/100000000000000 : ℝ)^7
        have hw : |(2829862909/5000000000 : ℝ)|=(2829862909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-596374741/2000000000 : ℝ)|^9 ≤ (10551478533233/50000000000000 : ℝ)^7
        have hw : |(-596374741/2000000000 : ℝ)|=(596374741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-400081863/1000000000 : ℝ)|^9 ≤ (1539739017249/5000000000000 : ℝ)^7
        have hw : |(-400081863/1000000000 : ℝ)|=(400081863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s1_s1_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (566225309/1000000000 : ℝ)*x 0 + (-907671659/10000000000 : ℝ)*x 1 + (1396478287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (566225309/1000000000 : ℝ)^9 ≤ (6016235088963/12500000000000 : ℝ)^7 := by
    have hnat : (566225309 : ℕ)^9*12500000000000^7 ≤ 6016235088963^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566225309 1000000000 6016235088963 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (907671659/10000000000 : ℝ)^9 ≤ (91458512859/2000000000000 : ℝ)^7 := by
    have hnat : (907671659 : ℕ)^9*2000000000000^7 ≤ 91458512859^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907671659 10000000000 91458512859 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1396478287/2500000000 : ℝ)^9 ≤ (1182429840927/2500000000000 : ℝ)^7 := by
    have hnat : (1396478287 : ℕ)^9*2500000000000^7 ≤ 1182429840927^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396478287 2500000000 1182429840927 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(566225309/1000000000 : ℝ), (-907671659/10000000000 : ℝ), (1396478287/2500000000 : ℝ)] ![(6016235088963/12500000000000 : ℝ), (91458512859/2000000000000 : ℝ), (1182429840927/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(566225309/1000000000 : ℝ)|^9 ≤ (6016235088963/12500000000000 : ℝ)^7
        have hw : |(566225309/1000000000 : ℝ)|=(566225309/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-907671659/10000000000 : ℝ)|^9 ≤ (91458512859/2000000000000 : ℝ)^7
        have hw : |(-907671659/10000000000 : ℝ)|=(907671659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1396478287/2500000000 : ℝ)|^9 ≤ (1182429840927/2500000000000 : ℝ)^7
        have hw : |(1396478287/2500000000 : ℝ)|=(1396478287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s1_s1_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1043679/250000000 : ℝ)*x 0 + (-658446029/1250000000 : ℝ)*x 1 + (3187375729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1043679/250000000 : ℝ)^9 ≤ (17451632411/20000000000000 : ℝ)^7 := by
    have hnat : (1043679 : ℕ)^9*20000000000000^7 ≤ 17451632411^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043679 250000000 17451632411 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658446029/1250000000 : ℝ)^9 ≤ (2193008033943/5000000000000 : ℝ)^7 := by
    have hnat : (658446029 : ℕ)^9*5000000000000^7 ≤ 2193008033943^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658446029 1250000000 2193008033943 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3187375729/5000000000 : ℝ)^9 ≤ (11210516229311/20000000000000 : ℝ)^7 := by
    have hnat : (3187375729 : ℕ)^9*20000000000000^7 ≤ 11210516229311^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3187375729 5000000000 11210516229311 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1043679/250000000 : ℝ), (-658446029/1250000000 : ℝ), (3187375729/5000000000 : ℝ)] ![(17451632411/20000000000000 : ℝ), (2193008033943/5000000000000 : ℝ), (11210516229311/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1043679/250000000 : ℝ)|^9 ≤ (17451632411/20000000000000 : ℝ)^7
        have hw : |(1043679/250000000 : ℝ)|=(1043679/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-658446029/1250000000 : ℝ)|^9 ≤ (2193008033943/5000000000000 : ℝ)^7
        have hw : |(-658446029/1250000000 : ℝ)|=(658446029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3187375729/5000000000 : ℝ)|^9 ≤ (11210516229311/20000000000000 : ℝ)^7
        have hw : |(3187375729/5000000000 : ℝ)|=(3187375729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s1_s1_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4496906879/10000000000 : ℝ)*x 0 + (3517880089/10000000000 : ℝ)*x 1 + (2361125527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4496906879/10000000000 : ℝ)^9 ≤ (17894371112873/50000000000000 : ℝ)^7 := by
    have hnat : (4496906879 : ℕ)^9*50000000000000^7 ≤ 17894371112873^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496906879 10000000000 17894371112873 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3517880089/10000000000 : ℝ)^9 ≤ (26100392663869/100000000000000 : ℝ)^7 := by
    have hnat : (3517880089 : ℕ)^9*100000000000000^7 ≤ 26100392663869^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3517880089 10000000000 26100392663869 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2361125527/5000000000 : ℝ)^9 ≤ (38110865095527/100000000000000 : ℝ)^7 := by
    have hnat : (2361125527 : ℕ)^9*100000000000000^7 ≤ 38110865095527^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2361125527 5000000000 38110865095527 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4496906879/10000000000 : ℝ), (3517880089/10000000000 : ℝ), (2361125527/5000000000 : ℝ)] ![(17894371112873/50000000000000 : ℝ), (26100392663869/100000000000000 : ℝ), (38110865095527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4496906879/10000000000 : ℝ)|^9 ≤ (17894371112873/50000000000000 : ℝ)^7
        have hw : |(4496906879/10000000000 : ℝ)|=(4496906879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3517880089/10000000000 : ℝ)|^9 ≤ (26100392663869/100000000000000 : ℝ)^7
        have hw : |(3517880089/10000000000 : ℝ)|=(3517880089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2361125527/5000000000 : ℝ)|^9 ≤ (38110865095527/100000000000000 : ℝ)^7
        have hw : |(2361125527/5000000000 : ℝ)|=(2361125527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s1_s1_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3612447817/5000000000 : ℝ)*x 0 + (-1073827739/5000000000 : ℝ)*x 1 + (-2895469469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3612447817/5000000000 : ℝ)^9 ≤ (65841200832343/100000000000000 : ℝ)^7 := by
    have hnat : (3612447817 : ℕ)^9*100000000000000^7 ≤ 65841200832343^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3612447817 5000000000 65841200832343 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073827739/5000000000 : ℝ)^9 ≤ (3459691460721/25000000000000 : ℝ)^7 := by
    have hnat : (1073827739 : ℕ)^9*25000000000000^7 ≤ 3459691460721^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073827739 5000000000 3459691460721 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2895469469/10000000000 : ℝ)^9 ≤ (20320033313261/100000000000000 : ℝ)^7 := by
    have hnat : (2895469469 : ℕ)^9*100000000000000^7 ≤ 20320033313261^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2895469469 10000000000 20320033313261 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3612447817/5000000000 : ℝ), (-1073827739/5000000000 : ℝ), (-2895469469/10000000000 : ℝ)] ![(65841200832343/100000000000000 : ℝ), (3459691460721/25000000000000 : ℝ), (20320033313261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3612447817/5000000000 : ℝ)|^9 ≤ (65841200832343/100000000000000 : ℝ)^7
        have hw : |(3612447817/5000000000 : ℝ)|=(3612447817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1073827739/5000000000 : ℝ)|^9 ≤ (3459691460721/25000000000000 : ℝ)^7
        have hw : |(-1073827739/5000000000 : ℝ)|=(1073827739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2895469469/10000000000 : ℝ)|^9 ≤ (20320033313261/100000000000000 : ℝ)^7
        have hw : |(-2895469469/10000000000 : ℝ)|=(2895469469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s1_s1_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (40579391/62500000 : ℝ)*x 0 + (-529796987/2000000000 : ℝ)*x 1 + (3347536413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40579391/62500000 : ℝ)^9 ≤ (896711669591/1562500000000 : ℝ)^7 := by
    have hnat : (40579391 : ℕ)^9*1562500000000^7 ≤ 896711669591^7*62500000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40579391 62500000 896711669591 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529796987/2000000000 : ℝ)^9 ≤ (18123624542793/100000000000000 : ℝ)^7 := by
    have hnat : (529796987 : ℕ)^9*100000000000000^7 ≤ 18123624542793^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529796987 2000000000 18123624542793 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3347536413/10000000000 : ℝ)^9 ≤ (4897365717863/20000000000000 : ℝ)^7 := by
    have hnat : (3347536413 : ℕ)^9*20000000000000^7 ≤ 4897365717863^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3347536413 10000000000 4897365717863 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(40579391/62500000 : ℝ), (-529796987/2000000000 : ℝ), (3347536413/10000000000 : ℝ)] ![(896711669591/1562500000000 : ℝ), (18123624542793/100000000000000 : ℝ), (4897365717863/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(40579391/62500000 : ℝ)|^9 ≤ (896711669591/1562500000000 : ℝ)^7
        have hw : |(40579391/62500000 : ℝ)|=(40579391/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-529796987/2000000000 : ℝ)|^9 ≤ (18123624542793/100000000000000 : ℝ)^7
        have hw : |(-529796987/2000000000 : ℝ)|=(529796987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3347536413/10000000000 : ℝ)|^9 ≤ (4897365717863/20000000000000 : ℝ)^7
        have hw : |(3347536413/10000000000 : ℝ)|=(3347536413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s1_s1_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1384269/400000000 : ℝ)*x 0 + (-7798363839/10000000000 : ℝ)*x 1 + (45532647/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1384269/400000000 : ℝ)^9 ≤ (68558846567/100000000000000 : ℝ)^7 := by
    have hnat : (1384269 : ℕ)^9*100000000000000^7 ≤ 68558846567^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384269 400000000 68558846567 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7798363839/10000000000 : ℝ)^9 ≤ (36317617756297/50000000000000 : ℝ)^7 := by
    have hnat : (7798363839 : ℕ)^9*50000000000000^7 ≤ 36317617756297^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7798363839 10000000000 36317617756297 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45532647/125000000 : ℝ)^9 ≤ (3412025703847/12500000000000 : ℝ)^7 := by
    have hnat : (45532647 : ℕ)^9*12500000000000^7 ≤ 3412025703847^7*125000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45532647 125000000 3412025703847 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1384269/400000000 : ℝ), (-7798363839/10000000000 : ℝ), (45532647/125000000 : ℝ)] ![(68558846567/100000000000000 : ℝ), (36317617756297/50000000000000 : ℝ), (3412025703847/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1384269/400000000 : ℝ)|^9 ≤ (68558846567/100000000000000 : ℝ)^7
        have hw : |(1384269/400000000 : ℝ)|=(1384269/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7798363839/10000000000 : ℝ)|^9 ≤ (36317617756297/50000000000000 : ℝ)^7
        have hw : |(-7798363839/10000000000 : ℝ)|=(7798363839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(45532647/125000000 : ℝ)|^9 ≤ (3412025703847/12500000000000 : ℝ)^7
        have hw : |(45532647/125000000 : ℝ)|=(45532647/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s1_s1_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1423070327/2000000000 : ℝ)*x 0 + (1392661707/5000000000 : ℝ)*x 1 + (2416863283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1423070327/2000000000 : ℝ)^9 ≤ (64560481111431/100000000000000 : ℝ)^7 := by
    have hnat : (1423070327 : ℕ)^9*100000000000000^7 ≤ 64560481111431^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423070327 2000000000 64560481111431 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1392661707/5000000000 : ℝ)^9 ≤ (3866327716013/20000000000000 : ℝ)^7 := by
    have hnat : (1392661707 : ℕ)^9*20000000000000^7 ≤ 3866327716013^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392661707 5000000000 3866327716013 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2416863283/10000000000 : ℝ)^9 ≤ (8053940150249/50000000000000 : ℝ)^7 := by
    have hnat : (2416863283 : ℕ)^9*50000000000000^7 ≤ 8053940150249^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416863283 10000000000 8053940150249 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1423070327/2000000000 : ℝ), (1392661707/5000000000 : ℝ), (2416863283/10000000000 : ℝ)] ![(64560481111431/100000000000000 : ℝ), (3866327716013/20000000000000 : ℝ), (8053940150249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1423070327/2000000000 : ℝ)|^9 ≤ (64560481111431/100000000000000 : ℝ)^7
        have hw : |(1423070327/2000000000 : ℝ)|=(1423070327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1392661707/5000000000 : ℝ)|^9 ≤ (3866327716013/20000000000000 : ℝ)^7
        have hw : |(1392661707/5000000000 : ℝ)|=(1392661707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2416863283/10000000000 : ℝ)|^9 ≤ (8053940150249/50000000000000 : ℝ)^7
        have hw : |(2416863283/10000000000 : ℝ)|=(2416863283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s1_s1_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (875253057/2000000000 : ℝ)*x 0 + (-4684856703/10000000000 : ℝ)*x 1 + (-1843140469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875253057/2000000000 : ℝ)^9 ≤ (8639763059139/25000000000000 : ℝ)^7 := by
    have hnat : (875253057 : ℕ)^9*25000000000000^7 ≤ 8639763059139^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875253057 2000000000 8639763059139 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4684856703/10000000000 : ℝ)^9 ≤ (37723288360417/100000000000000 : ℝ)^7 := by
    have hnat : (4684856703 : ℕ)^9*100000000000000^7 ≤ 37723288360417^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4684856703 10000000000 37723288360417 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1843140469/5000000000 : ℝ)^9 ≤ (13858829691267/50000000000000 : ℝ)^7 := by
    have hnat : (1843140469 : ℕ)^9*50000000000000^7 ≤ 13858829691267^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843140469 5000000000 13858829691267 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875253057/2000000000 : ℝ), (-4684856703/10000000000 : ℝ), (-1843140469/5000000000 : ℝ)] ![(8639763059139/25000000000000 : ℝ), (37723288360417/100000000000000 : ℝ), (13858829691267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875253057/2000000000 : ℝ)|^9 ≤ (8639763059139/25000000000000 : ℝ)^7
        have hw : |(875253057/2000000000 : ℝ)|=(875253057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4684856703/10000000000 : ℝ)|^9 ≤ (37723288360417/100000000000000 : ℝ)^7
        have hw : |(-4684856703/10000000000 : ℝ)|=(4684856703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1843140469/5000000000 : ℝ)|^9 ≤ (13858829691267/50000000000000 : ℝ)^7
        have hw : |(-1843140469/5000000000 : ℝ)|=(1843140469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310045_s1_s1_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1699182757/2500000000 : ℝ)*x 0 + (-826679641/5000000000 : ℝ)*x 1 + (1921708571/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1699182757/2500000000 : ℝ)^9 ≤ (60867550085589/100000000000000 : ℝ)^7 := by
    have hnat : (1699182757 : ℕ)^9*100000000000000^7 ≤ 60867550085589^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699182757 2500000000 60867550085589 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (826679641/5000000000 : ℝ)^9 ≤ (395460929561/4000000000000 : ℝ)^7 := by
    have hnat : (826679641 : ℕ)^9*4000000000000^7 ≤ 395460929561^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826679641 5000000000 395460929561 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1921708571/5000000000 : ℝ)^9 ≤ (14622963326021/50000000000000 : ℝ)^7 := by
    have hnat : (1921708571 : ℕ)^9*50000000000000^7 ≤ 14622963326021^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921708571 5000000000 14622963326021 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1699182757/2500000000 : ℝ), (-826679641/5000000000 : ℝ), (1921708571/5000000000 : ℝ)] ![(60867550085589/100000000000000 : ℝ), (395460929561/4000000000000 : ℝ), (14622963326021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1699182757/2500000000 : ℝ)|^9 ≤ (60867550085589/100000000000000 : ℝ)^7
        have hw : |(1699182757/2500000000 : ℝ)|=(1699182757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-826679641/5000000000 : ℝ)|^9 ≤ (395460929561/4000000000000 : ℝ)^7
        have hw : |(-826679641/5000000000 : ℝ)|=(826679641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1921708571/5000000000 : ℝ)|^9 ≤ (14622963326021/50000000000000 : ℝ)^7
        have hw : |(1921708571/5000000000 : ℝ)|=(1921708571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310045_s1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((19403/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19403/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2464/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-2464/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3553/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3553/4000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1093/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1093/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2363/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-2363/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68203/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(68203/100000 : ℝ)*X 1 2) := by
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
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s1_pow0 : (19403/25000 : ℝ) ^ (35/8 : ℝ) ≤ (6598858621201347477/20000000000000000000 : ℝ) := by
    have hpowers : (19403/25000 : ℝ)^35 ≤ (6598858621201347477/20000000000000000000 : ℝ)^8 := by
      have hnat : (19403 : ℕ)^35*20000000000000000000^8 ≤ 6598858621201347477^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19403 25000 6598858621201347477 20000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19403/25000 : ℝ)) (X := (6598858621201347477/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (26598858621201347477/20000000000000000000 : ℝ) ≤ (2668361682769129/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (26598858621201347477/20000000000000000000 : ℝ)^8 ≤ (2668361682769129/2500000000000000 : ℝ)^35 := by
      have hnat : (26598858621201347477 : ℕ)^8*2500000000000000^35 ≤ 2668361682769129^35*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26598858621201347477 20000000000000000000 2668361682769129 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2668361682769129/2500000000000000 : ℝ)) (X := (26598858621201347477/20000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (16598858621201347477/10000000000000000000 : ℝ) ≤ (561401538964223/500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (16598858621201347477/10000000000000000000 : ℝ)^8 ≤ (561401538964223/500000000000000 : ℝ)^35 := by
      have hnat : (16598858621201347477 : ℕ)^8*500000000000000^35 ≤ 561401538964223^35*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16598858621201347477 10000000000000000000 561401538964223 500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (561401538964223/500000000000000 : ℝ)) (X := (16598858621201347477/10000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(168361682769129/1940300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(69323006025993/970150000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (19403/25000 : ℝ)) (alpha := (168361682769129/1940300000000000 : ℝ)) (beta := (69323006025993/970150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (19403/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(168361682769129/1940300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(69323006025993/970150000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (2464/3125 : ℝ) ^ (35/8 : ℝ) ≤ (35355683128648122761/100000000000000000000 : ℝ) := by
    have hpowers : (2464/3125 : ℝ)^35 ≤ (35355683128648122761/100000000000000000000 : ℝ)^8 := by
      have hnat : (2464 : ℕ)^35*100000000000000000000^8 ≤ 35355683128648122761^8*3125^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2464 3125 35355683128648122761 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2464/3125 : ℝ)) (X := (35355683128648122761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (135355683128648122761/100000000000000000000 : ℝ) ≤ (10716470438610531/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (135355683128648122761/100000000000000000000 : ℝ)^8 ≤ (10716470438610531/10000000000000000 : ℝ)^35 := by
      have hnat : (135355683128648122761 : ℕ)^8*10000000000000000^35 ≤ 10716470438610531^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        135355683128648122761 100000000000000000000 10716470438610531 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10716470438610531/10000000000000000 : ℝ)) (X := (135355683128648122761/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (85355683128648122761/50000000000000000000 : ℝ) ≤ (706266447274629/625000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (85355683128648122761/50000000000000000000 : ℝ)^8 ≤ (706266447274629/625000000000000 : ℝ)^35 := by
      have hnat : (85355683128648122761 : ℕ)^8*625000000000000^35 ≤ 706266447274629^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85355683128648122761 50000000000000000000 706266447274629 625000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (706266447274629/625000000000000 : ℝ)) (X := (85355683128648122761/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(65133676237321/716800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(583792717783533/7884800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (2464/3125 : ℝ)) (alpha := (65133676237321/716800000000000 : ℝ)) (beta := (583792717783533/7884800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (2464/3125 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(65133676237321/716800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(583792717783533/7884800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (3553/4000 : ℝ) ^ (35/8 : ℝ) ≤ (59544488743689370127/100000000000000000000 : ℝ) := by
    have hpowers : (3553/4000 : ℝ)^35 ≤ (59544488743689370127/100000000000000000000 : ℝ)^8 := by
      have hnat : (3553 : ℕ)^35*100000000000000000000^8 ≤ 59544488743689370127^8*4000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3553 4000 59544488743689370127 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3553/4000 : ℝ)) (X := (59544488743689370127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (159544488743689370127/100000000000000000000 : ℝ) ≤ (556343462015751/500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (159544488743689370127/100000000000000000000 : ℝ)^8 ≤ (556343462015751/500000000000000 : ℝ)^35 := by
      have hnat : (159544488743689370127 : ℕ)^8*500000000000000^35 ≤ 556343462015751^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        159544488743689370127 100000000000000000000 556343462015751 500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (556343462015751/500000000000000 : ℝ)) (X := (159544488743689370127/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (109544488743689370127/50000000000000000000 : ℝ) ≤ (11963441238740929/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (109544488743689370127/50000000000000000000 : ℝ)^8 ≤ (11963441238740929/10000000000000000 : ℝ)^35 := by
      have hnat : (109544488743689370127 : ℕ)^8*10000000000000000^35 ≤ 11963441238740929^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109544488743689370127 50000000000000000000 11963441238740929 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11963441238740929/10000000000000000 : ℝ)) (X := (109544488743689370127/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(56343462015751/444125000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(44030105180311/467500000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (3553/4000 : ℝ)) (alpha := (56343462015751/444125000000000 : ℝ)) (beta := (44030105180311/467500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (3553/4000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(56343462015751/444125000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(44030105180311/467500000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((5599777731/10000000000 : ℝ)*X 1 0+(1669563849/5000000000 : ℝ)*X 1 1+(932577749/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1369028043/2500000000 : ℝ)*X 0 0+(-379755761/1250000000 : ℝ)*X 0 1+(2075020567/5000000000 : ℝ)*X 0 2+(1369028043/2500000000 : ℝ)*X 1 0+(-379755761/1250000000 : ℝ)*X 1 1+(2075020567/5000000000 : ℝ)*X 1 2+(1369028043/2500000000 : ℝ)*X 2 0+(-379755761/1250000000 : ℝ)*X 2 1+(2075020567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((1591053/500000000 : ℝ)*X 0 0+(-1940620073/2500000000 : ℝ)*X 0 1+(1843915899/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((36089359/80000000 : ℝ)*X 1 0+(192315319/500000000 : ℝ)*X 1 1+(879819619/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2829862909/5000000000 : ℝ)*X 2 0+(-596374741/2000000000 : ℝ)*X 2 1+(-400081863/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((566225309/1000000000 : ℝ)*X 0 0+(-907671659/10000000000 : ℝ)*X 0 1+(1396478287/2500000000 : ℝ)*X 0 2+(566225309/1000000000 : ℝ)*X 1 0+(-907671659/10000000000 : ℝ)*X 1 1+(1396478287/2500000000 : ℝ)*X 1 2+(566225309/1000000000 : ℝ)*X 2 0+(-907671659/10000000000 : ℝ)*X 2 1+(1396478287/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((1043679/250000000 : ℝ)*X 0 0+(-658446029/1250000000 : ℝ)*X 0 1+(3187375729/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4496906879/10000000000 : ℝ)*X 1 0+(3517880089/10000000000 : ℝ)*X 1 1+(2361125527/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3612447817/5000000000 : ℝ)*X 2 0+(-1073827739/5000000000 : ℝ)*X 2 1+(-2895469469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((40579391/62500000 : ℝ)*X 0 0+(-529796987/2000000000 : ℝ)*X 0 1+(3347536413/10000000000 : ℝ)*X 0 2+(40579391/62500000 : ℝ)*X 1 0+(-529796987/2000000000 : ℝ)*X 1 1+(3347536413/10000000000 : ℝ)*X 1 2+(40579391/62500000 : ℝ)*X 2 0+(-529796987/2000000000 : ℝ)*X 2 1+(3347536413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((1384269/400000000 : ℝ)*X 0 0+(-7798363839/10000000000 : ℝ)*X 0 1+(45532647/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1423070327/2000000000 : ℝ)*X 1 0+(1392661707/5000000000 : ℝ)*X 1 1+(2416863283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((875253057/2000000000 : ℝ)*X 2 0+(-4684856703/10000000000 : ℝ)*X 2 1+(-1843140469/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1699182757/2500000000 : ℝ)*X 0 0+(-826679641/5000000000 : ℝ)*X 0 1+(1921708571/5000000000 : ℝ)*X 0 2+(1699182757/2500000000 : ℝ)*X 1 0+(-826679641/5000000000 : ℝ)*X 1 1+(1921708571/5000000000 : ℝ)*X 1 2+(1699182757/2500000000 : ℝ)*X 2 0+(-826679641/5000000000 : ℝ)*X 2 1+(1921708571/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310045_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((1093/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1093/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (62336073834600966556086951/10927769600000000000000000000000 : ℝ) := by norm_num
    linear_combination (253354786491/1000000000000 : ℝ)*(base7) + (252689779581/1000000000000 : ℝ)*(base40) + (260307079047/500000000000 : ℝ)*(base50) + (2763898680277/1000000000000 : ℝ)*(major_s1_0) + (2763898680277/1000000000000 : ℝ)*(major_s1_1) + (2763898680277/1000000000000 : ℝ)*(major_s1_2) + (20330329/500000000000 : ℝ)*(sp_s1_6) + (3666522448811/1000000000000 : ℝ)*(sp_s1_7) + (3666549200319/1000000000000 : ℝ)*(sp_s1_8) + (733308797771/200000000000 : ℝ)*(sp_s1_9) + (980803620641/500000000000 : ℝ)*(sp_s1_13) + (29610227/1000000000000 : ℝ)*(sp_s1_14) + (1429359/500000000000 : ℝ)*(sp_s1_15) + (4035091/500000000000 : ℝ)*(sp_s1_23) + (213536639431/125000000000 : ℝ)*(f.failure) + (3666552059037/1000000000000 : ℝ)*(f.sum) + (200244834398591207/1819136000000000000000000000000 : ℝ)*base63 + (500464145265353/467500000000000000000000000 : ℝ)*base65 + (1453125644474617/1126400000000000000000000000 : ℝ)*base66 + (460989203565421/888250000000000000000000000 : ℝ)*base68 + (762397971851499233/4535451250000000000000000000000 : ℝ)*base70 + (33505344774857/485075000000000000000000000 : ℝ)*base72 + (11973626124709/102400000000000000000000000 : ℝ)*base74 + (50655946204623/1940300000000000000000000000 : ℝ)*base77 + (5696794550499760243/21855539200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (2717/12500000000000000 : ℝ)*base86 + (2717/12500000000000000 : ℝ)*base88 + (2717/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2363/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-2363/4000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (170214676959709256560998674667/19302880520000000000000000000000000 : ℝ) := by norm_num
    linear_combination (149959236097/200000000000 : ℝ)*(base7) + (5235953/1000000000000 : ℝ)*(base24) + (134854371581/250000000000 : ℝ)*(base40) + (2094153/1000000000000 : ℝ)*(base60) + (1360209941011/500000000000 : ℝ)*(major_s1_0) + (1360209941011/500000000000 : ℝ)*(major_s1_1) + (1360209941011/500000000000 : ℝ)*(major_s1_2) + (55559607/1000000000000 : ℝ)*(sp_s1_1) + (2463483/1000000000000 : ℝ)*(sp_s1_7) + (330676239379/100000000000 : ℝ)*(sp_s1_14) + (1653354648833/500000000000 : ℝ)*(sp_s1_15) + (82668990533/25000000000 : ℝ)*(sp_s1_16) + (1215585084367/500000000000 : ℝ)*(sp_s1_20) + (46024991/1000000000000 : ℝ)*(sp_s1_27) + (42035500331/25000000000 : ℝ)*(f.failure) + (3306764857273/1000000000000 : ℝ)*(f.sum) + (583040004881842807/6366976000000000000000000000000 : ℝ)*base63 + (42788481419921/233750000000000000000000000 : ℝ)*base64 + (1974910592251543/3942400000000000000000000000 : ℝ)*base67 + (420279815951869/888250000000000000000000000 : ℝ)*base69 + (338378296936761419/2267725625000000000000000000000 : ℝ)*base70 + (344248950658423/485075000000000000000000000 : ℝ)*base73 + (115215278090411/358400000000000000000000000 : ℝ)*base75 + (676744824640901/970150000000000000000000000 : ℝ)*base76 + (23439974729361622717/76494387200000000000000000000000 : ℝ)*base79 + (1517/2500000000000000 : ℝ)*base86 + (1517/2500000000000000 : ℝ)*base88 + (1517/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68203/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(68203/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2534094070363287955898005149/650202291200000000000000000000000 : ℝ) := by norm_num
    linear_combination (809158534877/1000000000000 : ℝ)*(base7) + (567056268621/1000000000000 : ℝ)*(base40) + (718047/200000000000 : ℝ)*(base43) + (36443790381/250000000000 : ℝ)*(base50) + (115381797441/40000000000 : ℝ)*(major_s1_0) + (288454134579/100000000000 : ℝ)*(major_s1_1) + (115381797441/40000000000 : ℝ)*(major_s1_2) + (108554069/250000000000 : ℝ)*(sp_s1_7) + (4291/400000000 : ℝ)*(sp_s1_16) + (5337679/1000000000000 : ℝ)*(sp_s1_20) + (3497300364379/1000000000000 : ℝ)*(sp_s1_21) + (3497738170891/1000000000000 : ℝ)*(sp_s1_22) + (699544770631/200000000000 : ℝ)*(sp_s1_23) + (2592014591711/1000000000000 : ℝ)*(sp_s1_27) + (1782861394513/1000000000000 : ℝ)*(f.failure) + (3497738170891/1000000000000 : ℝ)*(f.sum) + (62407342341345429/254679040000000000000000000000 : ℝ)*base62 + (12583588626351/18700000000000000000000000 : ℝ)*base64 + (627611696819511/788480000000000000000000000 : ℝ)*base67 + (888669052433/35530000000000000000000000 : ℝ)*base69 + (3174346275776657/5669314062500000000000000000 : ℝ)*base70 + (103257732273139/194030000000000000000000000 : ℝ)*base73 + (1659519947919/14336000000000000000000000 : ℝ)*base75 + (333376297101963/388060000000000000000000000 : ℝ)*base76 + (2848502929822912697/3059775488000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (58191/100000000000000000 : ℝ)*base86 + (58191/100000000000000000 : ℝ)*base88 + (58191/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((19403/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19403/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2464/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-2464/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3553/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3553/4000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1093/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1093/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2363/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-2363/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68203/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(68203/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310045_s1 p hpa hpb X hX hprev0

#print axioms solution

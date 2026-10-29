-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313086_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:35:40.040459+00:00
-- url     : https://prove2.me/submissions/ffc49d8a-b389-49c0-a3b5-30a38d45a343

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
theorem collision_support_c313086_s1_s1_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1181541043/2000000000 : ℝ)*x 0 + (-3402928133/10000000000 : ℝ)*x 1 + (-1614039721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1181541043/2000000000 : ℝ)^37 ≤ (51093062909461/100000000000000 : ℝ)^29 := by
    have hnat : (1181541043 : ℕ)^37*100000000000000^29 ≤ 51093062909461^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181541043 2000000000 51093062909461 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3402928133/10000000000 : ℝ)^37 ≤ (25276021482691/100000000000000 : ℝ)^29 := by
    have hnat : (3402928133 : ℕ)^37*100000000000000^29 ≤ 25276021482691^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3402928133 10000000000 25276021482691 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1614039721/5000000000 : ℝ)^37 ≤ (23630915592673/100000000000000 : ℝ)^29 := by
    have hnat : (1614039721 : ℕ)^37*100000000000000^29 ≤ 23630915592673^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614039721 5000000000 23630915592673 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1181541043/2000000000 : ℝ), (-3402928133/10000000000 : ℝ), (-1614039721/5000000000 : ℝ)] ![(51093062909461/100000000000000 : ℝ), (25276021482691/100000000000000 : ℝ), (23630915592673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1181541043/2000000000 : ℝ)|^37 ≤ (51093062909461/100000000000000 : ℝ)^29
        have hw : |(1181541043/2000000000 : ℝ)|=(1181541043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3402928133/10000000000 : ℝ)|^37 ≤ (25276021482691/100000000000000 : ℝ)^29
        have hw : |(-3402928133/10000000000 : ℝ)|=(3402928133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1614039721/5000000000 : ℝ)|^37 ≤ (23630915592673/100000000000000 : ℝ)^29
        have hw : |(-1614039721/5000000000 : ℝ)|=(1614039721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313086_s1_s1_6 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1977853751/5000000000 : ℝ)*x 0 + (-2827938819/10000000000 : ℝ)*x 1 + (719359831/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1977853751/5000000000 : ℝ)^37 ≤ (15313822246367/50000000000000 : ℝ)^29 := by
    have hnat : (1977853751 : ℕ)^37*50000000000000^29 ≤ 15313822246367^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977853751 5000000000 15313822246367 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2827938819/10000000000 : ℝ)^37 ≤ (9979789839671/50000000000000 : ℝ)^29 := by
    have hnat : (2827938819 : ℕ)^37*50000000000000^29 ≤ 9979789839671^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2827938819 10000000000 9979789839671 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (719359831/1250000000 : ℝ)^37 ≤ (24706387912131/50000000000000 : ℝ)^29 := by
    have hnat : (719359831 : ℕ)^37*50000000000000^29 ≤ 24706387912131^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719359831 1250000000 24706387912131 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1977853751/5000000000 : ℝ), (-2827938819/10000000000 : ℝ), (719359831/1250000000 : ℝ)] ![(15313822246367/50000000000000 : ℝ), (9979789839671/50000000000000 : ℝ), (24706387912131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1977853751/5000000000 : ℝ)|^37 ≤ (15313822246367/50000000000000 : ℝ)^29
        have hw : |(1977853751/5000000000 : ℝ)|=(1977853751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2827938819/10000000000 : ℝ)|^37 ≤ (9979789839671/50000000000000 : ℝ)^29
        have hw : |(-2827938819/10000000000 : ℝ)|=(2827938819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(719359831/1250000000 : ℝ)|^37 ≤ (24706387912131/50000000000000 : ℝ)^29
        have hw : |(719359831/1250000000 : ℝ)|=(719359831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313086_s1_s1_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-571/2000000000 : ℝ)*x 0 + (-732722009/1000000000 : ℝ)*x 1 + (4169159321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (571/2000000000 : ℝ)^37 ≤ (111737/25000000000000 : ℝ)^29 := by
    have hnat : (571 : ℕ)^37*25000000000000^29 ≤ 111737^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571 2000000000 111737 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (732722009/1000000000 : ℝ)^37 ≤ (67248266724859/100000000000000 : ℝ)^29 := by
    have hnat : (732722009 : ℕ)^37*100000000000000^29 ≤ 67248266724859^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732722009 1000000000 67248266724859 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4169159321/10000000000 : ℝ)^37 ≤ (6550346563661/20000000000000 : ℝ)^29 := by
    have hnat : (4169159321 : ℕ)^37*20000000000000^29 ≤ 6550346563661^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169159321 10000000000 6550346563661 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-571/2000000000 : ℝ), (-732722009/1000000000 : ℝ), (4169159321/10000000000 : ℝ)] ![(111737/25000000000000 : ℝ), (67248266724859/100000000000000 : ℝ), (6550346563661/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-571/2000000000 : ℝ)|^37 ≤ (111737/25000000000000 : ℝ)^29
        have hw : |(-571/2000000000 : ℝ)|=(571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-732722009/1000000000 : ℝ)|^37 ≤ (67248266724859/100000000000000 : ℝ)^29
        have hw : |(-732722009/1000000000 : ℝ)|=(732722009/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4169159321/10000000000 : ℝ)|^37 ≤ (6550346563661/20000000000000 : ℝ)^29
        have hw : |(4169159321/10000000000 : ℝ)|=(4169159321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313086_s1_s1_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5953369751/10000000000 : ℝ)*x 0 + (1655948591/5000000000 : ℝ)*x 1 + (204127099/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5953369751/10000000000 : ℝ)^37 ≤ (51597477705817/100000000000000 : ℝ)^29 := by
    have hnat : (5953369751 : ℕ)^37*100000000000000^29 ≤ 51597477705817^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5953369751 10000000000 51597477705817 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1655948591/5000000000 : ℝ)^37 ≤ (24416547309633/100000000000000 : ℝ)^29 := by
    have hnat : (1655948591 : ℕ)^37*100000000000000^29 ≤ 24416547309633^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1655948591 5000000000 24416547309633 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204127099/625000000 : ℝ)^37 ≤ (4797194994303/20000000000000 : ℝ)^29 := by
    have hnat : (204127099 : ℕ)^37*20000000000000^29 ≤ 4797194994303^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204127099 625000000 4797194994303 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5953369751/10000000000 : ℝ), (1655948591/5000000000 : ℝ), (204127099/625000000 : ℝ)] ![(51597477705817/100000000000000 : ℝ), (24416547309633/100000000000000 : ℝ), (4797194994303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5953369751/10000000000 : ℝ)|^37 ≤ (51597477705817/100000000000000 : ℝ)^29
        have hw : |(5953369751/10000000000 : ℝ)|=(5953369751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1655948591/5000000000 : ℝ)|^37 ≤ (24416547309633/100000000000000 : ℝ)^29
        have hw : |(1655948591/5000000000 : ℝ)|=(1655948591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(204127099/625000000 : ℝ)|^37 ≤ (4797194994303/20000000000000 : ℝ)^29
        have hw : |(204127099/625000000 : ℝ)|=(204127099/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313086_s1_s1_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5797365329/10000000000 : ℝ)*x 0 + (-429660327/1250000000 : ℝ)*x 1 + (-3322813327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5797365329/10000000000 : ℝ)^37 ≤ (49878684554879/100000000000000 : ℝ)^29 := by
    have hnat : (5797365329 : ℕ)^37*100000000000000^29 ≤ 49878684554879^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5797365329 10000000000 49878684554879 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429660327/1250000000 : ℝ)^37 ≤ (25602042762179/100000000000000 : ℝ)^29 := by
    have hnat : (429660327 : ℕ)^37*100000000000000^29 ≤ 25602042762179^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429660327 1250000000 25602042762179 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3322813327/10000000000 : ℝ)^37 ≤ (24519272668623/100000000000000 : ℝ)^29 := by
    have hnat : (3322813327 : ℕ)^37*100000000000000^29 ≤ 24519272668623^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3322813327 10000000000 24519272668623 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5797365329/10000000000 : ℝ), (-429660327/1250000000 : ℝ), (-3322813327/10000000000 : ℝ)] ![(49878684554879/100000000000000 : ℝ), (25602042762179/100000000000000 : ℝ), (24519272668623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5797365329/10000000000 : ℝ)|^37 ≤ (49878684554879/100000000000000 : ℝ)^29
        have hw : |(5797365329/10000000000 : ℝ)|=(5797365329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429660327/1250000000 : ℝ)|^37 ≤ (25602042762179/100000000000000 : ℝ)^29
        have hw : |(-429660327/1250000000 : ℝ)|=(429660327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3322813327/10000000000 : ℝ)|^37 ≤ (24519272668623/100000000000000 : ℝ)^29
        have hw : |(-3322813327/10000000000 : ℝ)|=(3322813327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313086_s1_s1_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1337435291/5000000000 : ℝ)*x 0 + (-579529283/5000000000 : ℝ)*x 1 + (124723979/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337435291/5000000000 : ℝ)^37 ≤ (9295812114443/50000000000000 : ℝ)^29 := by
    have hnat : (1337435291 : ℕ)^37*50000000000000^29 ≤ 9295812114443^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337435291 5000000000 9295812114443 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (579529283/5000000000 : ℝ)^37 ≤ (1599070324349/25000000000000 : ℝ)^29 := by
    have hnat : (579529283 : ℕ)^37*25000000000000^29 ≤ 1599070324349^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579529283 5000000000 1599070324349 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124723979/156250000 : ℝ)^37 ≤ (75012094459601/100000000000000 : ℝ)^29 := by
    have hnat : (124723979 : ℕ)^37*100000000000000^29 ≤ 75012094459601^29*156250000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124723979 156250000 75012094459601 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337435291/5000000000 : ℝ), (-579529283/5000000000 : ℝ), (124723979/156250000 : ℝ)] ![(9295812114443/50000000000000 : ℝ), (1599070324349/25000000000000 : ℝ), (75012094459601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337435291/5000000000 : ℝ)|^37 ≤ (9295812114443/50000000000000 : ℝ)^29
        have hw : |(1337435291/5000000000 : ℝ)|=(1337435291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-579529283/5000000000 : ℝ)|^37 ≤ (1599070324349/25000000000000 : ℝ)^29
        have hw : |(-579529283/5000000000 : ℝ)|=(579529283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(124723979/156250000 : ℝ)|^37 ≤ (75012094459601/100000000000000 : ℝ)^29
        have hw : |(124723979/156250000 : ℝ)|=(124723979/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313086_s1_s1_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-130719/10000000000 : ℝ)*x 0 + (-5046287673/10000000000 : ℝ)*x 1 + (1635952189/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130719/10000000000 : ℝ)^37 ≤ (7345677/12500000000000 : ℝ)^29 := by
    have hnat : (130719 : ℕ)^37*12500000000000^29 ≤ 7345677^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130719 10000000000 7345677 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5046287673/10000000000 : ℝ)^37 ≤ (167144941911/400000000000 : ℝ)^29 := by
    have hnat : (5046287673 : ℕ)^37*400000000000^29 ≤ 167144941911^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5046287673 10000000000 167144941911 400000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1635952189/2500000000 : ℝ)^37 ≤ (11642741150839/20000000000000 : ℝ)^29 := by
    have hnat : (1635952189 : ℕ)^37*20000000000000^29 ≤ 11642741150839^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1635952189 2500000000 11642741150839 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130719/10000000000 : ℝ), (-5046287673/10000000000 : ℝ), (1635952189/2500000000 : ℝ)] ![(7345677/12500000000000 : ℝ), (167144941911/400000000000 : ℝ), (11642741150839/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130719/10000000000 : ℝ)|^37 ≤ (7345677/12500000000000 : ℝ)^29
        have hw : |(-130719/10000000000 : ℝ)|=(130719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5046287673/10000000000 : ℝ)|^37 ≤ (167144941911/400000000000 : ℝ)^29
        have hw : |(-5046287673/10000000000 : ℝ)|=(5046287673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1635952189/2500000000 : ℝ)|^37 ≤ (11642741150839/20000000000000 : ℝ)^29
        have hw : |(1635952189/2500000000 : ℝ)|=(1635952189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313086_s1_s1_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7470538807/10000000000 : ℝ)*x 0 + (654094299/2500000000 : ℝ)*x 1 + (505032937/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7470538807/10000000000 : ℝ)^37 ≤ (68930991659423/100000000000000 : ℝ)^29 := by
    have hnat : (7470538807 : ℕ)^37*100000000000000^29 ≤ 68930991659423^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7470538807 10000000000 68930991659423 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654094299/2500000000 : ℝ)^37 ≤ (18074486612921/100000000000000 : ℝ)^29 := by
    have hnat : (654094299 : ℕ)^37*100000000000000^29 ≤ 18074486612921^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654094299 2500000000 18074486612921 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (505032937/2500000000 : ℝ)^37 ≤ (12994521715593/100000000000000 : ℝ)^29 := by
    have hnat : (505032937 : ℕ)^37*100000000000000^29 ≤ 12994521715593^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505032937 2500000000 12994521715593 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7470538807/10000000000 : ℝ), (654094299/2500000000 : ℝ), (505032937/2500000000 : ℝ)] ![(68930991659423/100000000000000 : ℝ), (18074486612921/100000000000000 : ℝ), (12994521715593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7470538807/10000000000 : ℝ)|^37 ≤ (68930991659423/100000000000000 : ℝ)^29
        have hw : |(7470538807/10000000000 : ℝ)|=(7470538807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654094299/2500000000 : ℝ)|^37 ≤ (18074486612921/100000000000000 : ℝ)^29
        have hw : |(654094299/2500000000 : ℝ)|=(654094299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(505032937/2500000000 : ℝ)|^37 ≤ (12994521715593/100000000000000 : ℝ)^29
        have hw : |(505032937/2500000000 : ℝ)|=(505032937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313086_s1_s1_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3476290083/5000000000 : ℝ)*x 0 + (-639325327/2000000000 : ℝ)*x 1 + (-2113999467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3476290083/5000000000 : ℝ)^37 ≤ (62892676255291/100000000000000 : ℝ)^29 := by
    have hnat : (3476290083 : ℕ)^37*100000000000000^29 ≤ 62892676255291^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3476290083 5000000000 62892676255291 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639325327/2000000000 : ℝ)^37 ≤ (11668773358613/50000000000000 : ℝ)^29 := by
    have hnat : (639325327 : ℕ)^37*50000000000000^29 ≤ 11668773358613^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639325327 2000000000 11668773358613 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113999467/10000000000 : ℝ)^37 ≤ (22031643229/160000000000 : ℝ)^29 := by
    have hnat : (2113999467 : ℕ)^37*160000000000^29 ≤ 22031643229^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113999467 10000000000 22031643229 160000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3476290083/5000000000 : ℝ), (-639325327/2000000000 : ℝ), (-2113999467/10000000000 : ℝ)] ![(62892676255291/100000000000000 : ℝ), (11668773358613/50000000000000 : ℝ), (22031643229/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3476290083/5000000000 : ℝ)|^37 ≤ (62892676255291/100000000000000 : ℝ)^29
        have hw : |(3476290083/5000000000 : ℝ)|=(3476290083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-639325327/2000000000 : ℝ)|^37 ≤ (11668773358613/50000000000000 : ℝ)^29
        have hw : |(-639325327/2000000000 : ℝ)|=(639325327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2113999467/10000000000 : ℝ)|^37 ≤ (22031643229/160000000000 : ℝ)^29
        have hw : |(-2113999467/10000000000 : ℝ)|=(2113999467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313086_s1_s1_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2479716423/10000000000 : ℝ)*x 0 + (-930646027/5000000000 : ℝ)*x 1 + (7680806571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2479716423/10000000000 : ℝ)^37 ≤ (16878758763641/100000000000000 : ℝ)^29 := by
    have hnat : (2479716423 : ℕ)^37*100000000000000^29 ≤ 16878758763641^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2479716423 10000000000 16878758763641 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (930646027/5000000000 : ℝ)^37 ≤ (5852670188719/50000000000000 : ℝ)^29 := by
    have hnat : (930646027 : ℕ)^37*50000000000000^29 ≤ 5852670188719^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930646027 5000000000 5852670188719 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7680806571/10000000000 : ℝ)^37 ≤ (71415900842987/100000000000000 : ℝ)^29 := by
    have hnat : (7680806571 : ℕ)^37*100000000000000^29 ≤ 71415900842987^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7680806571 10000000000 71415900842987 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2479716423/10000000000 : ℝ), (-930646027/5000000000 : ℝ), (7680806571/10000000000 : ℝ)] ![(16878758763641/100000000000000 : ℝ), (5852670188719/50000000000000 : ℝ), (71415900842987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2479716423/10000000000 : ℝ)|^37 ≤ (16878758763641/100000000000000 : ℝ)^29
        have hw : |(2479716423/10000000000 : ℝ)|=(2479716423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-930646027/5000000000 : ℝ)|^37 ≤ (5852670188719/50000000000000 : ℝ)^29
        have hw : |(-930646027/5000000000 : ℝ)|=(930646027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7680806571/10000000000 : ℝ)|^37 ≤ (71415900842987/100000000000000 : ℝ)^29
        have hw : |(7680806571/10000000000 : ℝ)|=(7680806571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313086_s1_s1_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6581449/10000000000 : ℝ)*x 0 + (-897244469/1250000000 : ℝ)*x 1 + (868242631/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6581449/10000000000 : ℝ)^37 ≤ (8722020681/100000000000000 : ℝ)^29 := by
    have hnat : (6581449 : ℕ)^37*100000000000000^29 ≤ 8722020681^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6581449 10000000000 8722020681 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897244469/1250000000 : ℝ)^37 ≤ (6550536232943/10000000000000 : ℝ)^29 := by
    have hnat : (897244469 : ℕ)^37*10000000000000^29 ≤ 6550536232943^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897244469 1250000000 6550536232943 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (868242631/2000000000 : ℝ)^37 ≤ (8621478910257/25000000000000 : ℝ)^29 := by
    have hnat : (868242631 : ℕ)^37*25000000000000^29 ≤ 8621478910257^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868242631 2000000000 8621478910257 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6581449/10000000000 : ℝ), (-897244469/1250000000 : ℝ), (868242631/2000000000 : ℝ)] ![(8722020681/100000000000000 : ℝ), (6550536232943/10000000000000 : ℝ), (8621478910257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6581449/10000000000 : ℝ)|^37 ≤ (8722020681/100000000000000 : ℝ)^29
        have hw : |(6581449/10000000000 : ℝ)|=(6581449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-897244469/1250000000 : ℝ)|^37 ≤ (6550536232943/10000000000000 : ℝ)^29
        have hw : |(-897244469/1250000000 : ℝ)|=(897244469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(868242631/2000000000 : ℝ)|^37 ≤ (8621478910257/25000000000000 : ℝ)^29
        have hw : |(868242631/2000000000 : ℝ)|=(868242631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313086_s1_s1_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3569474407/5000000000 : ℝ)*x 0 + (1374276191/5000000000 : ℝ)*x 1 + (1171522007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3569474407/5000000000 : ℝ)^37 ≤ (65051529838417/100000000000000 : ℝ)^29 := by
    have hnat : (3569474407 : ℕ)^37*100000000000000^29 ≤ 65051529838417^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3569474407 5000000000 65051529838417 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374276191/5000000000 : ℝ)^37 ≤ (19247489534437/100000000000000 : ℝ)^29 := by
    have hnat : (1374276191 : ℕ)^37*100000000000000^29 ≤ 19247489534437^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374276191 5000000000 19247489534437 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1171522007/5000000000 : ℝ)^37 ≤ (1570098060243/10000000000000 : ℝ)^29 := by
    have hnat : (1171522007 : ℕ)^37*10000000000000^29 ≤ 1570098060243^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171522007 5000000000 1570098060243 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3569474407/5000000000 : ℝ), (1374276191/5000000000 : ℝ), (1171522007/5000000000 : ℝ)] ![(65051529838417/100000000000000 : ℝ), (19247489534437/100000000000000 : ℝ), (1570098060243/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3569474407/5000000000 : ℝ)|^37 ≤ (65051529838417/100000000000000 : ℝ)^29
        have hw : |(3569474407/5000000000 : ℝ)|=(3569474407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1374276191/5000000000 : ℝ)|^37 ≤ (19247489534437/100000000000000 : ℝ)^29
        have hw : |(1374276191/5000000000 : ℝ)|=(1374276191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1171522007/5000000000 : ℝ)|^37 ≤ (1570098060243/10000000000000 : ℝ)^29
        have hw : |(1171522007/5000000000 : ℝ)|=(1171522007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313086_s1_s1_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4869344317/10000000000 : ℝ)*x 0 + (-4385476073/10000000000 : ℝ)*x 1 + (-423555929/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4869344317/10000000000 : ℝ)^37 ≤ (3992596727869/10000000000000 : ℝ)^29 := by
    have hnat : (4869344317 : ℕ)^37*10000000000000^29 ≤ 3992596727869^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4869344317 10000000000 3992596727869 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4385476073/10000000000 : ℝ)^37 ≤ (34935160650497/100000000000000 : ℝ)^29 := by
    have hnat : (4385476073 : ℕ)^37*100000000000000^29 ≤ 34935160650497^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4385476073 10000000000 34935160650497 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423555929/1250000000 : ℝ)^37 ≤ (12569436026523/50000000000000 : ℝ)^29 := by
    have hnat : (423555929 : ℕ)^37*50000000000000^29 ≤ 12569436026523^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423555929 1250000000 12569436026523 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4869344317/10000000000 : ℝ), (-4385476073/10000000000 : ℝ), (-423555929/1250000000 : ℝ)] ![(3992596727869/10000000000000 : ℝ), (34935160650497/100000000000000 : ℝ), (12569436026523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4869344317/10000000000 : ℝ)|^37 ≤ (3992596727869/10000000000000 : ℝ)^29
        have hw : |(4869344317/10000000000 : ℝ)|=(4869344317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4385476073/10000000000 : ℝ)|^37 ≤ (34935160650497/100000000000000 : ℝ)^29
        have hw : |(-4385476073/10000000000 : ℝ)|=(4385476073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423555929/1250000000 : ℝ)|^37 ≤ (12569436026523/50000000000000 : ℝ)^29
        have hw : |(-423555929/1250000000 : ℝ)|=(423555929/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313086_s1_s1_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5686953891/10000000000 : ℝ)*x 0 + (-1904133323/10000000000 : ℝ)*x 1 + (961496503/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5686953891/10000000000 : ℝ)^37 ≤ (48669884534653/100000000000000 : ℝ)^29 := by
    have hnat : (5686953891 : ℕ)^37*100000000000000^29 ≤ 48669884534653^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5686953891 10000000000 48669884534653 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1904133323/10000000000 : ℝ)^37 ≤ (1506271254131/12500000000000 : ℝ)^29 := by
    have hnat : (1904133323 : ℕ)^37*12500000000000^29 ≤ 1506271254131^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904133323 10000000000 1506271254131 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961496503/2000000000 : ℝ)^37 ≤ (1227498294427/3125000000000 : ℝ)^29 := by
    have hnat : (961496503 : ℕ)^37*3125000000000^29 ≤ 1227498294427^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961496503 2000000000 1227498294427 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5686953891/10000000000 : ℝ), (-1904133323/10000000000 : ℝ), (961496503/2000000000 : ℝ)] ![(48669884534653/100000000000000 : ℝ), (1506271254131/12500000000000 : ℝ), (1227498294427/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5686953891/10000000000 : ℝ)|^37 ≤ (48669884534653/100000000000000 : ℝ)^29
        have hw : |(5686953891/10000000000 : ℝ)|=(5686953891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1904133323/10000000000 : ℝ)|^37 ≤ (1506271254131/12500000000000 : ℝ)^29
        have hw : |(-1904133323/10000000000 : ℝ)|=(1904133323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(961496503/2000000000 : ℝ)|^37 ≤ (1227498294427/3125000000000 : ℝ)^29
        have hw : |(961496503/2000000000 : ℝ)|=(961496503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313086_s1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((73521/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73521/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-20903/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-20903/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41753/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41753/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((35531/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35531/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-63423/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-63423/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58587/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(58587/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (176973/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (73521/100000 : ℝ) ^ (73/16 : ℝ) ≤ (24575481613207315497/100000000000000000000 : ℝ) := by
    have hpowers : (73521/100000 : ℝ)^73 ≤ (24575481613207315497/100000000000000000000 : ℝ)^16 := by
      have hnat : (73521 : ℕ)^73*100000000000000000000^16 ≤ 24575481613207315497^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73521 100000 24575481613207315497 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73521/100000 : ℝ)) (X := (24575481613207315497/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (124575481613207315497/100000000000000000000 : ℝ) ≤ (419736483816407/400000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (124575481613207315497/100000000000000000000 : ℝ)^16 ≤ (419736483816407/400000000000000 : ℝ)^73 := by
      have hnat : (124575481613207315497 : ℕ)^16*400000000000000^73 ≤ 419736483816407^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        124575481613207315497 100000000000000000000 419736483816407 400000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (419736483816407/400000000000000 : ℝ)) (X := (124575481613207315497/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (74575481613207315497/50000000000000000000 : ℝ) ≤ (1364473295495657/1250000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (74575481613207315497/50000000000000000000 : ℝ)^16 ≤ (1364473295495657/1250000000000000 : ℝ)^73 := by
      have hnat : (74575481613207315497 : ℕ)^16*1250000000000000^73 ≤ 1364473295495657^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74575481613207315497 50000000000000000000 1364473295495657 1250000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1364473295495657/1250000000000000 : ℝ)) (X := (74575481613207315497/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(19736483816407/294084000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(422374268555081/7352100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (73521/100000 : ℝ)) (alpha := (19736483816407/294084000000000 : ℝ)) (beta := (422374268555081/7352100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (73521/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(19736483816407/294084000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(422374268555081/7352100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (20903/25000 : ℝ) ^ (73/16 : ℝ) ≤ (44192700577447993703/100000000000000000000 : ℝ) := by
    have hpowers : (20903/25000 : ℝ)^73 ≤ (44192700577447993703/100000000000000000000 : ℝ)^16 := by
      have hnat : (20903 : ℕ)^73*100000000000000000000^16 ≤ 44192700577447993703^16*25000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20903 25000 44192700577447993703 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20903/25000 : ℝ)) (X := (44192700577447993703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (144192700577447993703/100000000000000000000 : ℝ) ≤ (10835198759309933/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (144192700577447993703/100000000000000000000 : ℝ)^16 ≤ (10835198759309933/10000000000000000 : ℝ)^73 := by
      have hnat : (144192700577447993703 : ℕ)^16*10000000000000000^73 ≤ 10835198759309933^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        144192700577447993703 100000000000000000000 10835198759309933 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10835198759309933/10000000000000000 : ℝ)) (X := (144192700577447993703/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (94192700577447993703/50000000000000000000 : ℝ) ≤ (11489055503556051/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (94192700577447993703/50000000000000000000 : ℝ)^16 ≤ (11489055503556051/10000000000000000 : ℝ)^73 := by
      have hnat : (94192700577447993703 : ℕ)^16*10000000000000000^73 ≤ 11489055503556051^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        94192700577447993703 50000000000000000000 11489055503556051 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11489055503556051/10000000000000000 : ℝ)) (X := (94192700577447993703/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(835198759309933/8361200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(326928372123059/4180600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (20903/25000 : ℝ)) (alpha := (835198759309933/8361200000000000 : ℝ)) (beta := (326928372123059/4180600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (20903/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(835198759309933/8361200000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(326928372123059/4180600000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (41753/50000 : ℝ) ^ (73/16 : ℝ) ≤ (43937659635172285803/100000000000000000000 : ℝ) := by
    have hpowers : (41753/50000 : ℝ)^73 ≤ (43937659635172285803/100000000000000000000 : ℝ)^16 := by
      have hnat : (41753 : ℕ)^73*100000000000000000000^16 ≤ 43937659635172285803^16*50000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41753 50000 43937659635172285803 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41753/50000 : ℝ)) (X := (43937659635172285803/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (143937659635172285803/100000000000000000000 : ℝ) ≤ (5415497679545607/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (143937659635172285803/100000000000000000000 : ℝ)^16 ≤ (5415497679545607/5000000000000000 : ℝ)^73 := by
      have hnat : (143937659635172285803 : ℕ)^16*5000000000000000^73 ≤ 5415497679545607^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        143937659635172285803 100000000000000000000 5415497679545607 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5415497679545607/5000000000000000 : ℝ)) (X := (143937659635172285803/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (93937659635172285803/50000000000000000000 : ℝ) ≤ (2296446003156951/2000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (93937659635172285803/50000000000000000000 : ℝ)^16 ≤ (2296446003156951/2000000000000000 : ℝ)^73 := by
      have hnat : (93937659635172285803 : ℕ)^16*2000000000000000^73 ≤ 2296446003156951^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93937659635172285803 50000000000000000000 2296446003156951 2000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2296446003156951/2000000000000000 : ℝ)) (X := (93937659635172285803/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(415497679545607/4175300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(651234656693541/8350600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (41753/50000 : ℝ)) (alpha := (415497679545607/4175300000000000 : ℝ)) (beta := (651234656693541/8350600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (41753/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(415497679545607/4175300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(651234656693541/8350600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_2 : ((1181541043/2000000000 : ℝ)*X 2 0+(-3402928133/10000000000 : ℝ)*X 2 1+(-1614039721/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313086_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1977853751/5000000000 : ℝ)*X 0 0+(-2827938819/10000000000 : ℝ)*X 0 1+(719359831/1250000000 : ℝ)*X 0 2+(1977853751/5000000000 : ℝ)*X 1 0+(-2827938819/10000000000 : ℝ)*X 1 1+(719359831/1250000000 : ℝ)*X 1 2+(1977853751/5000000000 : ℝ)*X 2 0+(-2827938819/10000000000 : ℝ)*X 2 1+(719359831/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313086_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-571/2000000000 : ℝ)*X 0 0+(-732722009/1000000000 : ℝ)*X 0 1+(4169159321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313086_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5953369751/10000000000 : ℝ)*X 1 0+(1655948591/5000000000 : ℝ)*X 1 1+(204127099/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313086_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5797365329/10000000000 : ℝ)*X 2 0+(-429660327/1250000000 : ℝ)*X 2 1+(-3322813327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313086_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1337435291/5000000000 : ℝ)*X 0 0+(-579529283/5000000000 : ℝ)*X 0 1+(124723979/156250000 : ℝ)*X 0 2+(1337435291/5000000000 : ℝ)*X 1 0+(-579529283/5000000000 : ℝ)*X 1 1+(124723979/156250000 : ℝ)*X 1 2+(1337435291/5000000000 : ℝ)*X 2 0+(-579529283/5000000000 : ℝ)*X 2 1+(124723979/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313086_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-130719/10000000000 : ℝ)*X 0 0+(-5046287673/10000000000 : ℝ)*X 0 1+(1635952189/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313086_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((7470538807/10000000000 : ℝ)*X 1 0+(654094299/2500000000 : ℝ)*X 1 1+(505032937/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313086_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3476290083/5000000000 : ℝ)*X 2 0+(-639325327/2000000000 : ℝ)*X 2 1+(-2113999467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313086_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2479716423/10000000000 : ℝ)*X 0 0+(-930646027/5000000000 : ℝ)*X 0 1+(7680806571/10000000000 : ℝ)*X 0 2+(2479716423/10000000000 : ℝ)*X 1 0+(-930646027/5000000000 : ℝ)*X 1 1+(7680806571/10000000000 : ℝ)*X 1 2+(2479716423/10000000000 : ℝ)*X 2 0+(-930646027/5000000000 : ℝ)*X 2 1+(7680806571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313086_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((6581449/10000000000 : ℝ)*X 0 0+(-897244469/1250000000 : ℝ)*X 0 1+(868242631/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313086_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3569474407/5000000000 : ℝ)*X 1 0+(1374276191/5000000000 : ℝ)*X 1 1+(1171522007/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313086_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4869344317/10000000000 : ℝ)*X 2 0+(-4385476073/10000000000 : ℝ)*X 2 1+(-423555929/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313086_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((5686953891/10000000000 : ℝ)*X 0 0+(-1904133323/10000000000 : ℝ)*X 0 1+(961496503/2000000000 : ℝ)*X 0 2+(5686953891/10000000000 : ℝ)*X 1 0+(-1904133323/10000000000 : ℝ)*X 1 1+(961496503/2000000000 : ℝ)*X 1 2+(5686953891/10000000000 : ℝ)*X 2 0+(-1904133323/10000000000 : ℝ)*X 2 1+(961496503/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313086_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((35531/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35531/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7047876238418131153672261/2049079284000000000000000000000 : ℝ) := by norm_num
    linear_combination (30442893993/125000000000 : ℝ)*(base7) + (2237/250000000000 : ℝ)*(base24) + (16565273289/62500000000 : ℝ)*(base40) + (356109/500000000000 : ℝ)*(base50) + (1637345027191/500000000000 : ℝ)*(major_s1_0) + (1637345027191/500000000000 : ℝ)*(major_s1_1) + (1637345027191/500000000000 : ℝ)*(major_s1_2) + (4473447200843/1000000000000 : ℝ)*(sp_s1_7) + (4473591701829/1000000000000 : ℝ)*(sp_s1_8) + (4473583926579/1000000000000 : ℝ)*(sp_s1_9) + (2175619060041/1000000000000 : ℝ)*(sp_s1_13) + (42811559/1000000000000 : ℝ)*(sp_s1_20) + (72250493/500000000000 : ℝ)*(sp_s1_21) + (3883151/500000000000 : ℝ)*(sp_s1_23) + (386423743931/200000000000 : ℝ)*(f.failure) + (4473591701829/1000000000000 : ℝ)*(f.sum) + (7213870621535598659/87276295900000000000000000000000 : ℝ)*base63 + (2133391056993689/4175300000000000000000000000 : ℝ)*base65 + (4140166201946877/4180600000000000000000000000 : ℝ)*base66 + (1072178593436033/2087650000000000000000000000 : ℝ)*base68 + (68793560174716071581/306972231300000000000000000000000 : ℝ)*base70 + (873150738666617/1838025000000000000000000000 : ℝ)*base72 + (146181742575051/2090300000000000000000000000 : ℝ)*base74 + (795680388827/735210000000000000000000000 : ℝ)*base77 + (7865835469266833773/61472378520000000000000000000000 : ℝ)*base78 + (6603/20000000000000000 : ℝ)*base86 + (6603/20000000000000000 : ℝ)*base88 + (6603/20000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-63423/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-63423/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16915409620564308666806521105679/4277760367242600000000000000000000000 : ℝ) := by norm_num
    linear_combination (765401677937/1000000000000 : ℝ)*(base7) + (569893/1000000000000 : ℝ)*(base33) + (322378627009/1000000000000 : ℝ)*(base40) + (109227683451/1000000000000 : ℝ)*(base60) + (2564081497051/1000000000000 : ℝ)*(major_s1_0) + (512816413389/200000000000 : ℝ)*(major_s1_1) + (512816413389/200000000000 : ℝ)*(major_s1_2) + (8387999/500000000000 : ℝ)*(sp_s1_2) + (7960067/1000000000000 : ℝ)*(sp_s1_6) + (2162787/40000000000 : ℝ)*(sp_s1_13) + (3163795899401/1000000000000 : ℝ)*(sp_s1_14) + (3163795329507/1000000000000 : ℝ)*(sp_s1_15) + (3163778553509/1000000000000 : ℝ)*(sp_s1_16) + (455637692151/200000000000 : ℝ)*(sp_s1_20) + (1512848812561/1000000000000 : ℝ)*(f.failure) + (3163795899401/1000000000000 : ℝ)*(f.sum) + (3269235217674968161/34910518360000000000000000000000 : ℝ)*base63 + (856647801279657/1670120000000000000000000000 : ℝ)*base64 + (976784919359089/1672240000000000000000000000 : ℝ)*base67 + (7614227617373/167012000000000000000000000 : ℝ)*base68 + (18630840972784220827/122788892520000000000000000000000 : ℝ)*base70 + (4598450198904161/7352100000000000000000000000 : ℝ)*base73 + (17721697378239/167224000000000000000000000 : ℝ)*base75 + (491768710718251/1470420000000000000000000000 : ℝ)*base76 + (145822806207571154017/614723785200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (126207/100000000000000000 : ℝ)*base87 + (26207/100000000000000000 : ℝ)*base89 + (26207/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58587/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(58587/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (141343436510339038457021352937/9548572248309375000000000000000000 : ℝ) := by norm_num
    linear_combination (366333194427/500000000000 : ℝ)*(base7) + (2271247/1000000000000 : ℝ)*(base17) + (79336161591/100000000000 : ℝ)*(base40) + (1791947/250000000000 : ℝ)*(base43) + (759499/250000000000 : ℝ)*(base50) + (459533150293/125000000000 : ℝ)*(major_s1_0) + (919064508639/250000000000 : ℝ)*(major_s1_1) + (459533150293/125000000000 : ℝ)*(major_s1_2) + (8679541/50000000000 : ℝ)*(sp_s1_15) + (11130003/500000000000 : ℝ)*(sp_s1_16) + (1187814172531/250000000000 : ℝ)*(sp_s1_21) + (950217599169/200000000000 : ℝ)*(sp_s1_22) + (2375617215059/500000000000 : ℝ)*(sp_s1_23) + (2901720771989/1000000000000 : ℝ)*(sp_s1_27) + (433810876627/200000000000 : ℝ)*(f.failure) + (593907982239/125000000000 : ℝ)*(f.sum) + (9460000792977747/136369212343750000000000000000 : ℝ)*base63 + (297180518893351/2087650000000000000000000000 : ℝ)*base64 + (392364164409537/2090300000000000000000000000 : ℝ)*base67 + (544261020291119/2087650000000000000000000000 : ℝ)*base69 + (2590411378118340737/21926587950000000000000000000000 : ℝ)*base71 + (30605662396099/525150000000000000000000000 : ℝ)*base72 + (52413982104093/522575000000000000000000000 : ℝ)*base75 + (8511857470973/105030000000000000000000000 : ℝ)*base77 + (3179823661831445387/21954420900000000000000000000000 : ℝ)*base79 + (349/20000000000000000 : ℝ)*base87 + (349/20000000000000000 : ℝ)*base89 + (349/20000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((73521/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73521/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-20903/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-20903/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41753/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41753/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((35531/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35531/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-63423/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-63423/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58587/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(58587/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313086_s1 p hpa hpb X hX hprev0

#print axioms solution
